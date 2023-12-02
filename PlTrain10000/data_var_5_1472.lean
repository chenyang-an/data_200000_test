variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42970523788958376318450421105 : (((p5 → (((p2 ∧ (True → ((p4 ∧ (((p1 → p2) ∨ p5) ∧ (p4 ∨ True))) ∨ p5))) ∧ ((p3 ∨ p3) ∨ False)) ∨ (p2 ∧ True))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234865074175749329015879938126 : ((p5 → (p1 → p3)) → ((p1 ∨ (p4 ∨ ((p3 ∧ (True ∨ p1)) → (p2 ∧ (((((p3 ∨ p4) ∧ (False → True)) ∨ p5) → p2) ∧ True))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172439828098647283297693880483 : ((((p2 ∧ (p5 ∧ p5)) ∧ True) ∨ (p3 → (p4 ∨ (p1 ∨ ((p2 ∧ p4) ∨ p3))))) ∨ (((((False → (p5 ∨ False)) ∧ True) ∨ True) → p2) ∨ p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164453781003662493536028035761 : ((((((p5 ∨ p1) ∨ p4) → (p3 → ((p3 → ((False ∨ True) ∨ p5)) ∨ True))) ∧ True) ∧ p3) ∨ (p3 → ((False ∨ True) ∨ ((p1 → False) ∧ False)))) := by
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
theorem thm_5_vars_261461654048149938283947051386 : ((p5 → p2) → ((p3 ∨ ((p4 → (p4 ∨ (False → p4))) ∨ p3)) → ((p1 ∧ False) ∨ ((((p3 → (p2 ∨ False)) → p4) ∧ p5) ∨ (True ∨ p2))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713050201669078606934501422235 : ((((p4 ∧ ((p3 → (False → p1)) ∧ False)) ∨ ((((p1 → (p5 ∨ ((p1 → (p1 → p3)) ∧ p4))) ∧ p1) ∨ (True → (p5 ∧ p3))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302710668934419779946675319853 : (False ∨ (p3 ∨ ((p2 ∨ (False ∨ True)) → ((((True ∧ ((False ∧ (((p2 ∨ True) ∧ p3) ∨ p2)) ∧ p3)) ∨ (False → (True ∨ p3))) ∧ True) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120727161059309740614292867646 : ((((((((True → p2) → True) → ((p4 ∧ False) ∧ (((True → (p1 ∧ p5)) ∧ p3) ∨ p2))) ∨ True) ∨ p2) → (True → False)) ∨ False) → (p4 ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (((((True → p2) → True) → ((p4 ∧ False) ∧ (((True → (p1 ∧ p5)) ∧ p3) ∨ p2))) ∨ True) ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732201165935394115112929362229 : ((((True ∧ p5) ∧ (((((p5 → (((p4 ∧ True) → p3) ∧ p1)) → (p4 ∨ False)) ∧ (p1 → (True ∧ ((False ∧ p4) ∧ p1)))) ∧ False) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629993762500824648209438629257 : ((((((True ∧ ((True ∧ p1) → p4)) ∨ ((((p3 ∨ (p3 ∧ p5)) ∨ (p3 → False)) ∧ p3) → (((False → True) → False) → p5))) ∨ p4) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338439839469261181726541898487 : (p1 → (((False ∨ p1) ∧ p1) ∧ ((((p2 ∨ ((p2 → p4) ∧ (((p3 ∨ p3) ∨ p2) ∧ p1))) ∨ (((p4 ∨ p3) → True) ∧ p2)) → p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204461963798703108910446647494 : ((((p3 ∨ (p1 ∧ p4)) ∧ True) ∨ p2) ∨ ((((p1 → ((p1 ∧ p1) ∧ (False ∨ ((p4 ∨ (p5 ∧ p4)) → (p2 ∨ True))))) → False) → p3) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → ((p1 ∧ p1) ∧ (False ∨ ((p4 ∨ (p5 ∧ p4)) → (p2 ∨ True))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228131991482061612008497905196 : ((p4 ∧ (p1 → False)) ∨ (((p5 ∧ p1) ∨ (((p5 → p4) ∧ p4) ∨ ((p4 ∨ (p3 → p2)) ∧ (False → p2)))) ∨ ((False ∧ (p1 ∧ p4)) → p4))) := by
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
theorem thm_5_vars_37395359341673044067881035145 : (((((p3 ∨ ((p3 ∧ (p2 ∨ p3)) → (False ∧ (p5 → ((p4 → (((p3 ∨ p5) ∨ p2) ∧ (p5 ∨ True))) → p4))))) → False) ∨ True) ∧ True) ∨ p4) := by
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
theorem thm_5_vars_615980736991718949654968846899 : (((((((((False → ((False ∧ True) ∨ p5)) → True) ∨ p5) ∨ p5) ∧ (p5 → p3)) → ((False → (p4 ∧ p2)) ∧ ((p3 ∨ p2) → p5))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251983766701445261511792832329 : ((p4 → False) ∨ (((False ∧ (p2 ∧ False)) ∨ (((p3 ∨ p2) ∨ True) ∨ (p1 ∨ (p1 ∧ False)))) → ((p5 ∨ True) ∨ ((True ∧ (False ∧ p1)) → p1)))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- False on the left can always be used.
        apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59073083956223810142492458909 : (((p5 ∧ False) ∨ (p4 ∧ (p5 → ((((p5 ∧ (True → p2)) ∧ p2) → p3) → ((p5 → p1) → ((False ∧ p5) ∧ ((p1 ∧ p2) → p4))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172794920540776431707587904207 : (((p2 → p4) → (True ∧ ((p4 ∧ p4) ∧ ((True → ((p3 → p5) ∨ p2)) → p2)))) ∨ (False → (((p5 ∧ p4) ∨ (p5 ∧ (False → p5))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114043924169777103337704783367 : (((((p4 ∧ (True ∨ False)) ∨ (((p2 ∧ (((False → True) ∨ p2) ∨ p4)) ∧ p5) ∨ False)) ∨ (p5 ∨ p2)) ∨ ((p5 → p2) ∨ p2)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356616996505663040343881289038 : (p5 → (((p2 ∨ (((True → p2) ∨ p3) ∨ p4)) ∨ p1) ∨ ((((False ∧ p3) ∨ (p4 ∧ (p2 ∧ False))) → ((True → False) ∧ p3)) ∨ (p4 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198645530178637159978089547454 : ((p3 ∨ ((p3 ∨ p1) ∧ ((p4 ∨ p3) ∧ p1))) ∨ (((p2 → (p4 ∧ False)) ∧ (p3 ∨ p3)) → (p5 ∨ (((p3 ∨ (True ∧ p5)) → p3) → True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257945098720900772466915010080 : ((p4 ∨ False) → ((True ∧ (p3 → p1)) → ((((True ∨ (p5 ∨ False)) ∧ p2) ∧ ((p5 ∧ (p5 → (True → p3))) ∧ (p5 ∧ p1))) ∨ (p4 ∧ True)))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205640703730820258033354234321 : (((p4 ∧ p3) ∨ ((p2 ∧ p5) ∧ p1)) ∨ (((((p5 ∧ p4) ∧ p4) ∧ True) ∧ False) → (p1 ∧ ((p1 ∨ (p3 ∧ p2)) → ((True ∧ p3) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h10
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h1.left
    let h13 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- False on the left can always be used.
    apply False.elim h13
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- Conjunctions on the left can always be decomposed.
    let h23 := h1.left
    let h24 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h25 := h23.left
    let h26 := h23.right
    -- Conjunctions on the left can always be decomposed.
    let h27 := h25.left
    let h28 := h25.right
    -- Conjunctions on the left can always be decomposed.
    let h29 := h27.left
    let h30 := h27.right
    -- False on the left can always be used.
    apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146474081234189441765501646618 : ((p3 ∨ (p3 ∨ ((((p1 → (True → (False → p3))) ∨ (((p4 ∨ (p5 → p2)) → p5) → True)) ∧ False) ∨ True))) ∧ ((p1 → (p3 ∧ False)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171466435506782564783624794155 : (((p1 ∨ ((((p1 ∧ p1) → ((p5 ∨ p5) ∨ p3)) → (False ∨ False)) ∧ p1)) ∧ p2) ∨ (((p3 ∨ p5) → (((p3 → True) ∧ p1) → p1)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323688074540856465653764284692 : (p5 ∨ ((p5 ∨ (p5 ∧ (p4 ∨ (((p2 ∧ (p5 ∨ ((p5 → (p3 → p5)) ∧ p2))) ∨ (p3 ∧ p1)) → p5)))) ∨ (((False → p3) ∨ p2) ∧ True))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589199712791992225756815080994 : (((((((((p3 ∨ ((p4 → p1) ∨ (True ∧ (p3 → p2)))) ∨ ((p5 ∧ p2) → p4)) ∨ (True ∧ p4)) ∨ (p5 ∧ False)) ∧ p5) → False) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186965642175882916295772113608 : ((((p4 → p5) → p5) ∨ (True → (p2 ∨ ((p2 → p4) ∨ p3)))) → ((p5 ∧ (False ∧ (((p5 ∨ False) ∧ p5) → (p3 ∧ True)))) ∨ (p1 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685423515936479252758435530494 : ((((((((p4 ∨ p4) ∨ (((False ∧ (p3 → p5)) → (p4 ∧ p1)) → True)) ∨ p3) → p2) ∧ p5) → (p4 ∨ (((p3 → p3) → p5) ∧ True))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668558473877141914160550937488 : (((((((p2 ∧ p4) ∨ p3) ∨ ((True → (p4 ∨ (((p2 → False) ∨ (False → (p2 ∨ False))) → True))) → p1)) ∧ p3) ∨ ((p4 ∧ p5) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_42489656540888194883110595233 : (((False ∨ (((False ∧ (True ∨ (p3 ∧ ((((p2 → False) ∨ (False → (p4 ∨ True))) ∧ False) ∨ (p1 ∨ (p1 ∨ p4)))))) ∧ p2) ∨ p3)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151232423940290591119370167582 : ((((True → (True → p3)) → (((p4 ∨ (p5 → ((p5 ∧ True) ∧ (p1 ∧ p2)))) ∧ p4) ∨ (p5 ∨ p4))) → p4) → (p1 → ((p1 ∨ p1) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136482446810740724636424097361 : ((((p1 ∨ p4) ∨ p4) ∧ ((p4 ∨ p2) ∨ (p3 → ((((True → ((p1 → p5) ∧ True)) → (p3 ∧ p1)) → p3) → p1)))) ∨ ((p4 ∧ p3) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133844442236767366939744479213 : (((True ∧ (((((((False → False) ∧ p3) ∨ p5) ∧ p3) ∨ (p4 → (p2 ∧ p1))) ∧ True) ∨ (p2 → (p3 ∧ p4)))) ∧ p4) ∨ ((True → True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680688167735849420963277238000 : ((((((p2 → (p3 ∨ p5)) ∧ p5) ∧ ((p2 → (p1 ∧ (False → (p5 ∨ (p1 → p1))))) ∧ (p1 ∨ p5))) → (p3 ∧ (p4 ∧ (p3 → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204370978136419693026797400276 : (((p3 ∨ (p2 ∨ (p1 ∨ p4))) ∧ p2) ∨ ((p5 → (((((False ∨ p2) ∧ False) ∧ p3) → (p4 → p2)) ∨ ((p1 → p2) → p3))) → (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43904010111593063468138300051 : ((((((((((False → ((p2 ∨ False) → p1)) ∧ False) ∨ p3) → p5) ∧ (p1 → p5)) ∨ ((True → p1) ∧ p4)) ∧ p5) ∨ (True ∧ p5)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198749329221999666850876138637 : ((True → (((p2 ∧ True) → (p4 ∧ False)) → p5)) ∨ (p1 ∨ (p4 → (p2 ∨ (p2 ∨ (p4 ∨ ((((p1 → (p3 ∨ p1)) ∧ p1) → p1) ∨ p4))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697128260447634596773601576608 : (((((p2 → (p1 ∧ (p5 ∨ True))) ∨ ((p4 → (p1 ∧ p4)) ∧ p3)) ∧ ((((p4 ∨ ((p3 → p3) ∨ True)) ∧ (False → p1)) ∧ False) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165997494024969992627342941067 : (((p4 ∧ p2) ∨ ((((p4 ∧ False) ∧ True) ∧ (False ∨ p5)) ∨ (False ∨ (p3 → (p1 → p2))))) ∨ (p4 ∨ (False → ((p1 → (p2 ∧ p3)) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118553073526281608344553583160 : ((p3 ∨ (p1 → ((((p5 ∨ p4) ∨ (p4 ∧ (p2 ∧ (((p1 ∨ p4) ∨ p4) ∧ p5)))) ∨ (p4 → p1)) ∨ ((p2 ∨ p3) ∨ p4)))) ∨ (p5 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153082386417445657088928718565 : ((p3 ∧ ((p3 ∧ p1) → ((True ∧ (True ∨ p1)) → (p2 → ((p5 ∨ ((True → p3) ∧ p4)) ∨ (p1 → False)))))) → (((p3 → True) → p4) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (p3 → True) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117159555405074332850797705666 : ((True ∧ (((((p5 → ((p3 ∨ (p1 → p3)) ∧ p1)) ∨ p2) ∧ True) ∧ ((p2 ∨ False) → (p4 → ((p1 → p4) ∨ p4)))) ∨ False)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42534127071591037277938787013 : (((p1 ∨ ((((p3 ∧ p4) ∨ (((True → (True ∧ p4)) ∧ (p1 ∧ p5)) ∧ False)) ∨ (p3 ∨ ((p2 ∨ (p4 ∧ p4)) ∨ p4))) → p3)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62643673261783302943110877804 : ((p4 ∧ ((p3 → ((True → p4) ∨ (((p1 ∧ (((p5 ∨ ((p3 ∧ ((True ∧ p4) → p5)) ∨ p3)) → p5) → p2)) ∨ p3) ∨ p3))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148863185520532966487865914181 : (((p4 ∨ (p5 → (False ∧ True))) ∧ ((True → ((p3 ∨ (p3 → ((False ∧ p4) ∧ True))) ∧ p2)) ∧ (p1 ∧ p1))) ∨ ((p3 → True) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183912161805906814830518519789 : (((True ∧ ((((p4 → p3) ∧ p3) → True) ∧ (p3 → p5))) ∧ p4) ∨ ((((False ∨ False) ∨ (p4 ∧ (p5 ∧ p1))) ∧ p5) ∨ (p2 ∨ (p4 → True)))) := by
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
theorem thm_5_vars_313837036024336841488687568299 : (p3 ∨ (((((((((True → (True ∨ p4)) ∧ p5) ∧ True) → (True → p2)) → (p4 ∧ p1)) ∧ (p3 ∧ p3)) ∨ p5) ∨ (p3 → p3)) ∧ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346897821639170939721078286416 : (p3 → ((((False ∧ False) ∧ ((((p2 → p4) ∨ (p3 → p2)) ∧ False) ∨ ((p3 ∨ p2) ∨ p5))) ∨ p5) ∨ ((((True ∧ False) ∧ p4) ∧ p5) → p1))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185603699944990035889522941659 : ((p5 ∨ (p1 → (p2 ∨ (((p4 → False) → (p4 ∨ p2)) ∧ p5)))) ∨ (True → ((False → False) ∧ (False ∨ (True ∨ ((p1 ∧ p3) ∨ (p3 → p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156975189132915743210740823719 : (((((((p4 ∨ (p3 ∨ p3)) ∧ True) → False) ∨ p4) ∧ ((p5 → p3) ∨ ((False ∧ False) ∧ p4))) ∨ True) ∨ (((True ∨ p1) → p2) ∧ (p2 → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157363402541511557898118216595 : (((p2 → (((False ∨ (((True → (p1 ∨ p2)) ∧ p1) ∨ True)) ∧ False) ∨ ((False → False) ∧ p3))) → False) ∨ (p5 ∨ ((p2 ∨ p3) ∨ (p3 → p3)))) := by
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
theorem thm_5_vars_451522670450823222516294548547 : (((((False ∧ (p1 ∨ ((p5 ∨ p1) ∨ (((p4 ∨ p1) ∧ (p4 ∧ p3)) ∧ p1)))) ∨ (p1 ∨ (False → p5))) ∨ (p5 ∨ ((p3 ∨ p5) ∨ p5))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157982323456232302492560789190 : (((((((p3 ∧ p5) ∨ p4) → p3) ∨ p2) ∨ p5) → (((p2 → ((True ∨ p2) ∧ p1)) ∧ p4) → p1)) ∨ ((p3 ∧ (False → (p4 → p1))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321232808486867162516678047701 : (p4 ∨ (p4 ∨ (((((True → ((p1 ∨ p5) ∧ (p3 ∧ ((p2 ∧ True) → p1)))) → p5) ∧ p2) ∨ (False ∨ (True ∨ ((p4 ∨ p1) ∨ p1)))) ∨ False))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171885203568949461832280867781 : (((False ∨ ((p4 ∨ p2) ∧ ((True → (p1 → (p4 → (p1 → p4)))) ∨ p5))) → p1) ∨ (p3 → ((p1 ∨ p2) → (p3 → (p4 → (False → p1)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225504939060966459347698376351 : (((p5 ∨ p3) ∧ True) ∨ ((((p5 ∧ False) ∨ ((p3 ∨ True) ∧ ((p5 → (p1 ∧ p2)) ∨ (p2 → ((p3 ∧ p4) ∨ (p4 ∨ p2)))))) ∨ p3) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_166770895810725491400445012516 : ((p5 → ((((p1 → (False ∨ p2)) ∧ True) → (p1 → ((p5 ∨ p3) ∨ (p1 ∧ p4)))) → False)) ∨ ((False → (False → (p5 ∨ p3))) ∨ (False ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49479078546502355029938425214 : ((((((p1 ∧ ((p1 → p4) ∧ p4)) ∧ ((((p4 ∨ p4) ∧ False) ∧ p5) → (False ∨ p5))) ∧ (p5 → p1)) → p2) → ((p2 → False) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648339364125584804879189629989 : (((((((p4 ∨ (((p4 ∨ True) → p4) → ((True ∧ p4) ∨ True))) ∧ ((((p3 ∨ True) → p4) ∨ p4) ∨ p1)) ∧ p4) ∨ p3) ∧ (True → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_925968891312354153233596891866 : ((((((False ∧ (((p2 ∧ p3) ∨ (p3 ∨ p3)) ∧ p1)) ∨ True) ∨ True) → (p4 ∧ ((True ∧ ((p4 ∨ ((False ∨ True) ∧ p2)) ∧ False)) ∧ p5))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False ∧ (((p2 ∧ p3) ∨ (p3 ∨ p3)) ∧ p1)) ∨ True) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165178568762654320521811938600 : (((p2 ∨ (((p2 ∧ (p4 → p2)) ∧ ((p4 → p2) ∧ (p1 ∧ p1))) ∧ p2)) ∧ (p2 ∨ p4)) ∨ ((True ∧ False) ∨ (p3 → ((False ∧ p3) ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300056037752294992781564253442 : (False ∨ ((((False ∨ (p3 ∨ p1)) ∧ ((True ∨ p3) → (p5 → (((p3 ∧ p3) → (False ∨ p2)) ∨ ((False ∧ p3) → p5))))) ∧ False) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126098878707964286784595099456 : ((True ∧ ((((True ∧ (p4 ∨ p3)) ∧ p4) ∨ (((True ∨ (p3 → p2)) ∧ ((((p5 ∧ False) ∧ True) ∧ p4) → p5)) ∨ p2)) → False)) → (False ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((True ∧ (p4 ∨ p3)) ∧ p4) ∨ (((True ∨ (p3 → p2)) ∧ ((((p5 ∧ False) ∧ True) ∧ p4) → p5)) ∨ p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- False on the left can always be used.
    apply False.elim h11
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h12 := h3 h4
  -- False on the left can always be used.
  apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
  have h15 : (((True ∧ (p4 ∨ p3)) ∧ p4) ∨ (((True ∨ (p3 → p2)) ∧ ((((p5 ∧ False) ∧ True) ∧ p4) → p5)) ∨ p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h16
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h19.left
    let h22 := h19.right
    -- False on the left can always be used.
    apply False.elim h22
  -- We have shown the premise of h14, we can now drive its conclusion.
  let h23 := h14 h15
  -- False on the left can always be used.
  apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_484179742386086439007035890848 : (((((p5 → (p1 ∨ True)) ∨ (True → False)) ∧ ((p1 → (True → (p2 ∨ ((((p3 ∧ p3) ∨ p4) ∨ p5) ∨ ((False ∨ p1) ∨ p1))))) ∨ p2)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159235212327077589666591089304 : ((p3 → (((((p3 → p1) ∨ True) ∧ (p5 ∧ ((p4 → p4) → p2))) ∨ (p2 ∨ (p4 → True))) → False)) ∨ (True ∨ (True ∨ ((p1 ∧ p5) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39296126780039558931157970139 : (((p1 ∧ (((p2 → (p1 → p5)) → p4) ∧ ((p2 ∨ (p2 → False)) → (((p1 ∨ (p4 ∨ p1)) ∧ p4) ∨ ((p5 ∧ p4) ∧ False))))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192400308565403019614712426548 : ((((p5 → (p4 ∨ ((p1 ∧ True) ∨ p4))) ∧ p1) ∨ p1) → ((p2 ∧ ((p5 ∨ p2) ∧ True)) ∨ (p1 ∨ ((p2 ∨ p2) → (p1 ∧ (True ∨ True)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660706610045892968139957193392 : ((((((p3 ∧ ((p2 ∧ False) ∧ (False ∨ (False ∨ p3)))) ∨ ((p4 ∨ (p1 ∨ (p1 ∧ ((p3 → p1) → p5)))) ∨ True)) → False) → (False ∨ p4)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∧ ((p2 ∧ False) ∧ (False ∨ (False ∨ p3)))) ∨ ((p4 ∨ (p1 ∨ (p1 ∧ ((p3 → p1) → p5)))) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179361907244114037318905485109 : ((p2 ∨ ((((True → p5) ∨ False) ∧ (True ∨ (p5 ∧ p5))) → (False ∨ p1))) ∨ ((False → p5) ∨ (((False ∨ p1) ∨ (p1 → (True ∨ p5))) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303046716975261156706387914083 : (False ∨ (p2 → ((p4 ∨ ((((p3 ∨ p1) → ((((True → p3) → p3) ∨ p3) ∧ False)) ∨ (((True ∧ p4) → p3) → (True → p5))) ∨ p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42696604017271396309827777634 : (((p5 ∨ ((p1 → ((p4 ∧ (p4 → ((False ∧ ((p3 ∨ p3) → (False ∨ ((p3 ∨ True) ∨ True)))) ∨ False))) ∨ p1)) → (p2 ∨ p2))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120034867774910195398820839786 : (((((((True ∨ False) → p3) ∧ (p4 ∨ (True → p3))) → True) ∨ (True ∨ ((True ∧ (p2 ∨ (p4 ∨ p4))) ∨ (True ∧ p2)))) ∧ True) → (p1 ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735312554328936313499282510074 : ((((p4 ∨ False) ∧ (((True ∨ (p1 ∧ ((p1 ∧ True) ∧ p5))) ∧ ((((False → ((p1 ∨ p3) ∧ (p4 ∨ p2))) ∨ p1) → p3) ∧ p5)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680954381375414125574184191966 : (((((p2 ∧ p5) ∨ ((((((False ∧ (p4 ∨ False)) ∧ (True ∨ p3)) → False) ∨ (p2 ∧ False)) ∨ p4) ∧ p5)) → (((p3 → p5) ∧ p5) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670604690346109787214748306036 : (((((p4 → False) ∨ (p3 ∧ (p3 ∨ (False → (((((p1 → True) ∧ ((p2 ∧ True) ∧ False)) ∨ p2) ∧ True) → p4))))) ∨ (p1 ∨ (p4 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159011899172379295595854620129 : ((p4 ∨ (((p2 → p5) ∨ (((p5 → ((True → (p2 ∧ p4)) ∧ (p5 ∧ p5))) → p4) → False)) → p4)) ∨ (((True ∧ True) → p1) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691000488651849729896794535984 : (((((p4 ∨ (((p2 → p1) → ((p3 → p5) → (p1 ∨ p4))) ∨ False)) → (False ∧ p5)) → ((((False ∨ p5) ∧ p1) ∨ p2) → (False ∨ p2))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h8 : (p4 ∨ (((p2 → p1) → ((p3 → p5) → (p1 ∨ p4))) ∨ False)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- Implications on the right can always be decomposed.
        intro h10
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h11 := h1 h8
      -- We need to get the left conjuct of h11 based on <expert-advice>.
      let h12 := h11.left
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159915877799403797324879289999 : (((((((p3 → (p4 ∨ (False ∨ (p4 ∧ p2)))) → p2) ∧ (True ∧ (p2 ∨ p4))) ∨ p2) → p2) → False) → (((False → p2) → (p4 ∨ p1)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p3 → (p4 ∨ (False ∨ (p4 ∧ p2)))) → p2) ∧ (True ∧ (p2 ∨ p4))) ∨ p2) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h11 : (p3 → (p4 ∨ (False ∨ (p4 ∧ p2)))) := by
          -- Implications on the right can always be decomposed.
          intro h12
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h13 := h5 h11
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h14
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h15 := h1 h2
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625030274047726022042666666 : (((p1 ∨ (((((p3 → True) ∨ (p4 ∧ p1)) ∨ ((((p5 ∧ (p3 → False)) ∨ p1) ∨ True) ∨ p5)) ∨ p1) → p1)) ∨ (True → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16927408226424620965443219502 : (((p5 ∧ (((False ∧ (False ∧ p4)) ∧ p5) ∧ ((False → (p2 ∧ (p5 ∧ (p2 ∧ True)))) ∧ ((p2 ∧ False) → False)))) ∨ (False ∨ (True ∨ p4))) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299386294645610243058630201888 : (False ∨ (((p2 → p2) → ((False ∨ ((p1 ∧ ((p1 ∧ (p5 → (p4 ∧ p1))) ∨ p4)) ∧ (p4 → True))) ∨ ((p2 ∧ (True ∧ False)) ∨ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218045173914629851145575560348 : (((p2 ∨ p3) ∧ (False ∨ p1)) → ((p4 ∨ (True ∨ (True ∨ (((p3 ∧ p2) → p3) ∨ ((False ∨ True) ∧ p4))))) → ((p2 ∧ (p5 ∧ p1)) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h1.left
      let h15 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h17 =>
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
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
      cases h22
      case inl h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h1.left
        let h25 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h26 =>
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h27 =>
            -- False on the left can always be used.
            apply False.elim h27
          case inr h28 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h29 =>
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h30 =>
            -- False on the left can always be used.
            apply False.elim h30
          case inr h31 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h32 =>
        -- Disjunctions on the left can always be decomposed.
        cases h32
        case inl h33 =>
          -- Conjunctions on the left can always be decomposed.
          let h34 := h1.left
          let h35 := h1.right
          -- Disjunctions on the left can always be decomposed.
          cases h34
          case inl h36 =>
            -- Disjunctions on the left can always be decomposed.
            cases h35
            case inl h37 =>
              -- False on the left can always be used.
              apply False.elim h37
            case inr h38 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h39 =>
            -- Disjunctions on the left can always be decomposed.
            cases h35
            case inl h40 =>
              -- False on the left can always be used.
              apply False.elim h40
            case inr h41 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
        case inr h42 =>
          -- Conjunctions on the left can always be decomposed.
          let h43 := h42.left
          let h44 := h42.right
          -- Disjunctions on the left can always be decomposed.
          cases h43
          case inl h45 =>
            -- False on the left can always be used.
            apply False.elim h45
          case inr h46 =>
            -- Conjunctions on the left can always be decomposed.
            let h47 := h1.left
            let h48 := h1.right
            -- Disjunctions on the left can always be decomposed.
            cases h47
            case inl h49 =>
              -- Disjunctions on the left can always be decomposed.
              cases h48
              case inl h50 =>
                -- False on the left can always be used.
                apply False.elim h50
              case inr h51 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
            case inr h52 =>
              -- Disjunctions on the left can always be decomposed.
              cases h48
              case inl h53 =>
                -- False on the left can always be used.
                apply False.elim h53
              case inr h54 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209205862697252525631547972679 : ((p4 ∨ (p1 ∧ (True ∨ (p4 → p4)))) → (((p3 ∧ (p1 → ((p3 ∨ False) ∨ p3))) ∧ p3) ∨ (p2 ∨ (True → ((p1 ∨ (p4 ∧ p1)) → True))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354607618544664273417637265585 : (p5 → ((((p3 ∨ (p4 → ((False → p1) ∧ (((p4 ∧ p3) → p5) → (((True ∨ p1) ∨ ((False ∧ p5) ∧ True)) ∨ p1))))) → False) ∨ p2) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339767453159398434190179236544 : (p1 → (p4 ∨ (False ∨ (((((p3 ∨ (p5 → ((p2 ∧ False) ∧ ((p1 → p1) ∨ p1)))) ∨ (False ∨ True)) ∧ p4) ∨ False) ∨ (p1 ∧ (False → p4)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328132667585353277897559607345 : (True → (((p5 ∧ p4) ∧ (((True → (p1 ∨ p1)) ∧ (((p4 ∧ p1) ∧ (p2 → (p3 ∨ p1))) → (p5 → p4))) ∧ p4)) ∨ (p4 → (p2 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_393115381316809676062980702498 : (((((p3 ∧ True) ∧ (True ∧ (((p5 ∨ ((p5 → ((p4 ∧ p2) → True)) → (p4 ∧ (True ∨ p4)))) ∧ p2) ∧ ((p3 → p3) ∨ p3)))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_257822500577147309750465540139 : ((p3 ∨ p5) → (((p1 ∨ p1) ∨ p3) ∨ (p1 ∨ ((p4 ∧ False) ∨ (p4 ∨ (False ∨ ((((p2 ∧ p3) → p1) ∨ p1) → ((p5 → p5) ∨ p5)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213474297035356517658094140229 : (((False → (p3 → p4)) ∧ p5) ∨ ((p5 → (p3 ∧ ((p3 ∨ p1) ∨ p3))) → ((((((p4 ∨ p4) ∨ p4) ∨ p2) ∧ p3) ∧ (p2 ∧ p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802919755457354522107011670912 : (((p3 → ((((True → ((p4 → (p5 ∧ ((p4 ∧ p3) → (p4 ∨ p5)))) ∧ (p3 → ((p2 ∨ p1) → (p1 → p5))))) → False) ∨ p3) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328789976816340183318913864469 : (True → (((p1 ∧ (p1 ∨ (False ∨ (p5 ∨ p3)))) ∧ (True ∧ p4)) ∨ ((((False ∧ (p1 → (p4 ∨ p1))) ∧ p5) ∧ p4) ∨ (False → (True ∧ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337054545038079037310953684976 : (p1 → (((p4 ∨ ((((True ∧ True) ∧ ((p1 ∨ True) ∨ (False ∨ ((False ∧ True) ∨ p3)))) → (p4 ∨ False)) ∧ (p3 ∨ p2))) ∨ True) ∨ (p3 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199271850635654357816319599458 : (((((False ∧ (p2 → p2)) → p4) ∧ False) ∨ True) → ((((p4 ∨ (p2 → (p4 ∨ (p2 → (p2 ∧ p4))))) → p5) ∨ (False → True)) ∧ (p1 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117221831987685449015829749151 : ((True ∧ ((p4 → False) ∧ ((((((((p2 ∧ p4) ∨ p5) ∨ ((p4 ∨ p3) ∧ (True → p2))) ∨ p2) ∨ p1) → False) → p4) ∧ p5))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313025256234810778258144099989 : (p3 ∨ (((p5 ∨ (p5 ∨ (p2 → ((((p4 ∨ p3) ∧ (p4 → True)) ∨ ((True ∧ p4) ∨ (p5 ∧ False))) ∧ (p4 → (True ∧ True)))))) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196654693372297196879213348929 : ((((((p1 ∧ p2) → True) → False) ∧ p5) ∧ p3) ∨ ((p2 ∧ p5) → ((p1 ∨ ((p2 → False) → ((True ∨ (p2 → p5)) ∧ (p4 ∧ False)))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47327149427259044436221662099 : ((((p4 ∨ (p5 → p4)) → ((p1 ∨ ((True → p3) ∧ (((p1 ∧ True) ∨ p1) ∧ False))) ∨ (False ∨ (p4 → (p1 ∨ p4))))) ∨ (p3 → p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66714014965712009465476222946 : ((True → ((p1 → p1) ∧ (((False ∨ p1) ∧ ((p4 ∨ ((p5 ∧ True) → True)) → ((True ∧ (False ∧ p1)) ∧ (True → (p4 ∧ False))))) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346782472459749709908298660331 : (p3 → ((((((False → p1) ∧ ((p1 ∨ False) ∨ p3)) → p3) → False) ∧ (((p4 ∨ p1) ∨ True) ∨ (True ∨ p4))) ∨ ((p3 ∧ p2) ∨ (True ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



