variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259354659024437832065320931886 : ((False → p2) → (p1 ∨ ((False → ((((True → p3) ∧ (p1 ∧ p5)) ∧ p5) ∨ p4)) ∧ ((p3 ∨ p1) ∨ (p2 ∨ ((p3 ∧ False) ∨ (False → p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190771971805002153127715862926 : ((((p5 → (p3 ∧ (True → p5))) ∧ p5) ∨ (p3 ∨ p1)) ∨ ((((p2 ∨ p4) ∨ (True ∧ (((p4 ∨ p1) ∧ p2) ∨ p2))) → False) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300570206504326673676794934498 : (False ∨ ((p1 ∨ ((False ∨ p1) ∨ (((p2 → ((True → False) → (p4 ∨ ((p4 ∨ p5) → True)))) ∨ True) ∧ True))) ∨ ((p1 → False) → (p3 → p1)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42559603277064166418373683260 : (((p1 ∨ (p3 ∨ (p2 ∧ (((p1 ∧ (((p5 → p1) ∧ p5) ∧ (p3 ∧ p5))) → (False ∧ p2)) → ((p4 → p5) ∧ (False ∧ p1)))))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112855307556426917402111259926 : (((((True → p2) ∧ p5) ∨ ((((p5 ∧ p2) ∨ (False → p3)) ∨ p5) ∧ (((p3 → p3) → (False ∨ p5)) ∧ (p2 → p3)))) → p5) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336407466749741791520354606223 : (p1 → ((p5 ∧ ((((p4 → (((((p5 ∨ p5) ∧ False) → False) ∧ ((p2 → (p4 ∨ p4)) ∧ p2)) → False)) ∧ p1) ∨ (p1 ∨ p4)) → False)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48850886112091749589155049616 : (((p2 ∨ ((p5 ∧ ((p3 ∧ True) ∧ p1)) ∨ ((p5 ∧ (((False ∧ p2) → p1) ∨ (False → p4))) → (True → p3)))) ∧ ((p5 ∨ p2) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769537424262714747123705871272 : (((p5 ∧ (p4 ∧ (((p4 ∧ (p2 ∨ (((False ∨ p3) ∨ p3) ∧ ((p4 → (False ∧ p5)) ∧ True)))) → ((p2 ∨ p2) → p1)) → (p5 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86586489194794497669621262944 : (((((True ∧ (p4 ∨ p3)) ∨ (False ∧ p4)) → False) ∧ (p4 ∧ (((p1 ∨ ((False ∧ (p5 ∨ False)) ∨ ((p1 ∧ p2) → p4))) ∨ p5) ∨ False))) → p2) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h9 : ((True ∧ (p4 ∨ p3)) ∨ (False ∧ p4)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h4
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h10 := h2 h9
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- False on the left can always be used.
          apply False.elim h13
        case inr h15 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h16 : ((True ∧ (p4 ∨ p3)) ∨ (False ∧ p4)) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h4
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h17 := h2 h16
          -- False on the left can always be used.
          apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h19 : ((True ∧ (p4 ∨ p3)) ∨ (False ∧ p4)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h20 := h2 h19
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351950255189106944441564827843 : (p4 → ((p2 ∨ (False ∧ ((False ∨ p2) ∧ (p3 ∨ (False ∨ False))))) → ((p3 ∨ ((((p5 → False) ∧ p3) ∧ (p3 ∧ (True → False))) ∧ False)) ∨ p4))) := by
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
    exact h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246072559322442207603648914010 : ((p4 ∧ p1) ∨ (((((False → p5) ∨ ((p3 ∧ True) ∨ (p5 ∧ p3))) ∧ p1) → (p2 ∧ ((p5 ∨ (p1 ∧ ((p1 ∧ True) ∧ p2))) ∨ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10224850044847573665845713650 : (((p2 ∨ ((False ∨ (p1 ∧ ((p3 ∨ p1) ∨ p3))) ∨ (p5 → ((True ∧ ((p1 ∧ p1) ∨ p1)) → (p3 ∨ ((False → p1) → p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345550047200875913164056794849 : (p3 → (((((False ∧ (p3 → p2)) → p1) ∧ p1) → (p2 ∧ (((((((p3 ∨ (p4 → False)) ∧ True) → p2) → p4) ∧ p3) ∨ p3) ∨ p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264205321284331886416112374979 : (True ∧ ((p2 ∧ ((p5 ∨ ((p4 ∨ True) ∨ False)) → p2)) → ((((True ∧ (p4 → True)) ∨ (p1 ∧ (p3 ∨ p5))) → p1) ∨ (p3 → (True ∧ p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314435075062179745171927675906 : (p3 ∨ ((p1 ∧ (p1 → (False ∨ (p5 → (((((p2 ∨ p3) ∨ (p4 ∧ (p2 → False))) ∧ p3) ∧ p3) → p2))))) ∨ ((False ∨ p3) ∨ (True ∨ p1)))) := by
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
theorem thm_5_vars_463549121751612239167840139040 : ((((p5 ∧ ((p3 → p5) ∧ ((p5 → p4) → ((p1 ∧ (p4 ∨ (p3 ∧ False))) ∧ p3)))) ∨ (False → (p4 → (False ∧ ((False ∨ False) ∧ p4))))) ∧ True) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55874579878834939482237634706 : (((True ∨ (False ∨ (p2 ∨ p2))) ∧ ((False ∨ (((p2 ∧ (True ∨ False)) → ((p1 ∧ (p4 ∧ False)) → p4)) → (p4 ∧ (p3 ∨ p4)))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257508026885056394039012019921 : ((p3 ∨ False) → (((((((p1 → (p3 ∨ p3)) ∨ (False ∧ (p2 ∨ p4))) ∧ p1) → p4) → False) ∨ True) ∨ ((p2 → (p2 ∨ (p1 → p3))) ∨ p5))) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44182030574328974614293632409 : ((((p5 ∨ (True ∨ (((p4 → ((True → (p4 ∨ p1)) → ((p5 ∨ p4) ∨ True))) ∨ p4) → (p3 ∧ p5)))) → ((p2 → False) ∧ p4)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90753976746278692180772293620 : (((p1 ∨ p5) ∧ (p4 ∧ ((p4 → ((p2 → ((True ∨ (p1 ∨ (p4 → p2))) ∧ p2)) ∧ p1)) ∧ (p2 → (False → (p2 ∨ (False ∧ p4))))))) → p1) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h14 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h15 := h12 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178308056095686877300694728759 : ((((False → (p1 ∨ (p5 → ((p4 ∧ p5) → p4)))) ∧ p4) ∨ (p1 ∨ p3)) ∨ ((p2 → (((p4 ∧ p3) ∨ (False → p1)) ∨ p4)) ∨ (p3 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714663760672284892885529390536 : (((((p5 ∧ p5) → (True → (p5 ∨ False))) → (p2 ∨ (((((True ∧ ((p4 ∨ False) ∧ p2)) ∨ p1) ∨ (p2 ∨ (False ∧ p5))) ∨ p1) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311890687042139538617596677388 : (p2 ∨ (p2 ∨ ((((True → False) → (p4 → False)) ∧ p5) ∨ (p1 ∨ ((p4 ∧ False) → (p3 ∧ ((False → p1) ∨ ((False ∨ (p5 ∧ p3)) → p1)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586249560970369092052888703456 : (((((((True ∨ (False → p5)) ∧ (((p4 ∧ p2) ∧ p2) ∧ True)) ∨ (True → (False ∧ (True → (p1 ∨ (p2 ∨ (False → False))))))) ∧ True) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246605584486805206061515611831 : ((p5 ∧ p2) ∨ (True → ((p3 ∧ p3) ∨ ((((p2 ∧ ((((p5 → p1) ∨ False) → True) ∨ p1)) ∧ p1) ∨ (p2 → (p3 → p3))) ∨ (p1 ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260769206367642363791231558132 : ((p3 → p5) → (((((p3 ∧ True) ∨ p4) ∨ (p1 ∨ (p3 → p2))) ∧ (False ∧ ((((p3 → p1) ∧ p4) ∧ p3) ∨ (p1 ∧ (p2 ∨ p5))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38191766176887400271983416390 : (((((((p2 ∨ ((p1 ∧ (p5 → (p3 ∨ p1))) ∧ False)) ∨ (p4 ∨ (p5 ∧ (p2 ∨ p4)))) ∨ p2) ∧ p4) → ((p2 ∧ False) ∧ p1)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166668120956562334266302587239 : ((p2 → ((p1 ∨ ((p5 → p3) ∨ ((p5 → (p4 ∧ p4)) ∨ ((True ∧ True) ∧ p1)))) ∧ p4)) ∨ (p4 ∨ ((p4 ∨ (p5 ∧ (p3 → p1))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788385534338784915680800679775 : (((p5 ∨ ((((True ∧ p2) → ((((((False ∨ p1) → p4) ∨ p3) → p2) → (p3 ∧ p4)) ∨ (p5 ∨ p3))) ∧ (p2 ∧ (p2 ∨ p3))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49024580954181034341864474176 : (((((True ∨ (p2 ∧ ((p2 ∨ (p5 ∧ p3)) ∧ True))) ∧ ((p2 ∧ ((p1 → False) → (False ∧ True))) → True)) → p2) ∨ (p4 ∧ (p3 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42701564558170461772983876783 : (((p5 ∨ (((p2 ∨ (((p2 ∧ p2) → (p5 → p4)) ∨ False)) → (False ∧ p1)) → (((p4 ∧ p5) → ((p4 → False) ∧ p3)) ∨ p4))) ∨ p3) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (p2 ∨ (((p2 ∧ p2) → (p5 → p4)) ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h6
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- False on the left can always be used.
  apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h2.left
  let h14 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h15 : (p2 ∨ (((p2 ∧ p2) → (p5 → p4)) ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h16
    -- Implications on the right can always be decomposed.
    intro h17
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h20 := h1 h15
  -- We need to get the left conjuct of h20 based on <expert-advice>.
  let h21 := h20.left
  -- False on the left can always be used.
  apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166474689412136817084237539130 : ((p3 ∨ ((((p5 → (p1 ∨ (p2 ∨ p4))) → ((p4 ∧ (True → p3)) → p5)) → p3) ∨ True)) ∨ ((p1 ∧ (p2 ∧ (p1 → (p5 ∧ p3)))) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57801008177661770826747543617 : (((p1 ∧ (p4 → p2)) → (((((p4 → (p1 → ((p4 ∧ ((p3 ∧ (p4 ∧ p4)) ∧ p3)) ∧ p5))) ∨ p5) ∧ p2) ∧ p5) ∨ (p5 → p5))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_898550970702251887663825318640 : (((((((p3 → True) → (((p5 ∨ (p1 ∧ (((p3 → p2) ∧ True) → p2))) ∨ p4) → p5)) ∨ (p5 ∨ True)) ∨ False) → ((p3 ∧ False) ∧ p1)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p3 → True) → (((p5 ∨ (p1 ∧ (((p3 → p2) ∧ True) → p2))) ∨ p4) → p5)) ∨ (p5 ∨ True)) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757168984976866266756356240150 : (((p1 ∧ (((False → p3) → p5) → ((p4 ∧ (p5 ∨ (p5 → (True ∨ ((((True → p4) → p2) ∧ (True → p1)) ∧ p1))))) ∧ (False ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58756301235004444440338327274 : (((p4 → False) ∧ (((((p3 → (p4 ∧ p3)) ∧ (p2 ∨ (p3 ∧ False))) ∨ False) ∧ p1) ∧ (((p5 ∨ (p5 → (p1 ∧ False))) ∨ False) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51872336090647780090294151551 : (((((True ∨ True) → ((((p3 ∧ p3) → p5) → p4) ∨ (False ∨ (p4 → True)))) ∨ p4) ∨ ((p4 ∨ (((False → p3) ∨ p3) → False)) → p5)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261140598781316315748775261921 : ((p4 → p4) → ((p2 ∧ (((((p3 → (p1 ∧ True)) ∨ (p4 ∨ (p2 ∧ p3))) ∨ True) ∨ ((True → ((p2 → True) ∧ p3)) → True)) → p5)) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((((p3 → (p1 ∧ True)) ∨ (p4 ∨ (p2 ∧ p3))) ∨ True) ∨ ((True → ((p2 → True) ∧ p3)) → True)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41244941051386989135024348423 : ((((((p1 ∨ (p5 ∨ ((False → (p4 → (p2 → False))) → ((False → p2) ∧ p5)))) ∧ p1) ∨ p2) ∨ (p1 → (p4 → (p1 → True)))) ∨ p3) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63331845225084489434411105782 : ((p5 ∧ ((p1 ∨ p5) → ((p1 → ((False → ((p3 ∨ p1) → p5)) → ((p4 ∨ True) ∨ True))) → (False ∨ ((p3 → (p1 → p2)) ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172602532014440969255322664517 : (((True ∨ (True ∧ True)) → (((p3 ∨ p5) ∧ (False ∨ (p5 ∨ True))) ∧ (p3 ∧ p5))) ∨ (((p2 ∨ (p2 ∧ (True → p5))) ∧ (False ∧ p4)) → p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200529714670015050239566784161 : (((p4 ∨ True) → ((p3 → p4) ∧ (p5 → p1))) → (((((p1 → (p4 ∨ p4)) ∨ (p3 → ((False → p5) ∨ (False ∨ True)))) ∨ p1) ∨ p4) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215597955370670700421128939002 : ((p5 ∧ (p3 ∨ (False ∧ p4))) ∨ (p3 → (p5 ∨ (False → ((((p4 → False) ∧ (p2 → p3)) ∧ p2) → (((p5 ∨ (p5 ∨ p4)) → p5) ∨ p3)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118324602949710063998292292294 : ((p2 ∨ ((((((((p2 ∨ p5) ∧ False) ∧ ((p2 ∧ p3) ∨ p5)) ∧ False) ∧ False) ∧ (p3 → (p2 → (False ∧ p3)))) ∧ p2) ∧ True)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2272488080156613622036294805 : ((((((((True ∨ p1) ∨ (True ∧ p4)) ∨ p1) ∧ p2) ∧ p3) ∨ p2) ∨ p2) ∨ ((True ∧ (p4 ∨ (p4 → (True ∧ p4)))) ∨ (p2 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147259357529298372070973066728 : ((((((((p2 ∨ (p3 → (False → ((False ∨ False) → False)))) ∧ (p1 ∧ p4)) ∧ True) ∨ False) ∧ p1) ∨ True) ∨ p5) ∨ (((False ∧ p5) ∧ p5) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319045517647156103994495064808 : (p4 ∨ (((p3 → ((p5 ∧ (p3 ∧ ((p4 → True) → p1))) ∧ p2)) → ((p4 → (True → (p4 ∧ p3))) ∨ False)) ∨ (((p2 → p1) ∨ True) ∨ p5))) := by
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
theorem thm_5_vars_42894257991125284270679628191 : (((p3 → ((((p5 ∨ p3) → (((((p1 ∧ (p4 → p1)) ∧ True) → p4) → False) ∧ p2)) ∧ (p5 → p1)) ∨ (True ∨ (p5 → p3)))) ∨ p4) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2096499207319897681717003611 : ((p4 ∧ ((p1 ∧ True) ∧ ((((p2 ∧ p5) ∧ p3) → p1) → ((False ∧ (p4 ∨ p2)) ∨ p2)))) ∨ ((p4 ∧ True) ∨ ((p4 ∧ False) → p1))) := by
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
theorem thm_5_vars_172634146231015068687407712721 : (((p5 ∧ False) ∧ ((False ∨ p5) ∧ (((p2 → p3) → (p1 → False)) → (True ∨ p5)))) ∨ (((((p2 ∨ True) ∧ p1) ∨ p5) → (True ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137159973066322749988592118970 : ((False ∧ (((p3 ∨ ((p1 → (p1 ∧ (p5 ∨ p1))) ∨ (((p3 ∨ True) → p5) ∨ ((p1 ∨ p3) ∨ p2)))) ∧ p3) → p5)) ∨ ((False ∨ p4) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_49873395039391369905863494559 : ((((((p4 → (((p1 ∧ p3) ∧ ((((False ∧ p5) ∨ p2) ∧ p2) → p5)) ∨ True)) ∨ True) ∧ p2) ∨ True) ∧ (False ∧ ((p5 ∧ p3) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731672440099338167010979343995 : ((((p2 → (p3 ∧ p1)) → (p3 ∨ (((((p4 ∨ (((False ∨ p5) ∧ (p1 ∨ p2)) ∧ p2)) → p3) → ((p1 ∧ p2) ∨ p1)) → False) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345649342176358801975610999594 : (p3 → ((p4 ∧ (((p4 ∧ (p5 ∨ (p4 → (((p5 ∨ p2) ∨ p1) ∨ p4)))) ∨ p2) ∧ (True ∨ ((False ∧ (p5 ∨ p1)) ∧ (p1 → p5))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110905832428398185767992213755 : ((((True ∧ ((((p4 ∧ p1) ∨ (p2 → p5)) → ((p1 ∧ p1) → ((p2 ∨ p2) → (False ∨ True)))) ∨ (False → p1))) → p1) ∧ True) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323794962854625674947246991829 : (p5 ∨ (((p1 → ((((False ∨ True) ∨ p1) ∧ p5) ∧ p3)) ∨ (((True → False) ∨ False) → (p2 ∨ p5))) ∨ ((False ∨ p3) ∧ ((p1 → p2) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214388908469944097919655293753 : (((True → (p3 → p2)) → p4) ∨ (p1 ∨ ((p3 → (p3 ∧ ((p3 → p5) ∧ (p3 ∨ True)))) → ((p3 ∧ p4) ∨ (p2 ∨ ((p3 → p3) ∨ False)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117050450958471300790268269645 : (((p4 ∨ p3) → (((((p2 ∨ ((((p1 → ((p1 ∧ p1) ∨ p1)) ∨ (p2 ∧ False)) ∨ p5) → p4)) → p4) ∨ p3) → p2) ∧ p1)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706615193304024300045437297078 : ((((p2 → ((p5 ∧ p3) → ((p4 → p3) ∧ p4))) ∧ ((False ∧ ((p3 ∧ ((p4 → (((p3 → p2) ∨ p2) ∧ p2)) ∨ True)) ∨ False)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167319838039531613065902960163 : (((((((p5 ∨ p5) → p1) ∨ p2) ∨ ((p5 ∨ p3) ∨ (p1 → False))) ∧ (p5 ∨ True)) → False) → (p4 → (p1 ∨ (((p5 → p2) ∨ False) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109530641309317108496791437670 : ((p3 ∨ (((p3 ∨ ((False → ((p3 ∧ p2) ∧ ((False ∨ False) ∧ (p1 ∨ p1)))) ∧ p5)) ∧ (((p2 ∨ p5) ∧ p3) → False)) ∨ True)) ∧ (True ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_323979820496915411668665983193 : (p5 ∨ (((((p5 ∧ (((p3 ∧ p2) ∧ True) ∨ p1)) ∨ p5) ∧ (False ∧ True)) ∧ p5) ∨ (p4 ∨ (p2 ∨ ((True ∨ (p1 ∨ (p4 ∧ p1))) ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_137508206305955791135074091711 : ((p5 ∧ ((p2 ∨ ((p5 ∨ p3) → ((p1 → False) ∨ ((p3 ∨ p5) ∧ p2)))) ∨ (p4 ∧ (p5 ∨ (p1 ∨ (False → p2)))))) ∨ (False → (p2 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42973542919862363136691335126 : (((p5 → ((((p3 → p1) ∧ (p4 ∧ (((False ∧ ((False → p3) → (True ∨ p3))) ∨ p2) ∨ False))) → p4) → ((True ∧ p1) → p3))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62205148476283878750384085190 : ((p3 ∧ ((((p5 → p1) ∧ p4) → (((((p2 ∧ ((p4 → True) ∧ ((p4 ∨ False) → (False → p1)))) → p1) ∨ p3) ∧ p5) ∨ p4)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663997702675145072532632356645 : ((((p5 ∧ ((False ∨ (p1 ∧ (p1 ∧ (((p2 → p1) → (True ∨ ((p4 → p2) → p5))) ∨ (False → (False ∧ False)))))) → p4)) → (p5 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55559149288209146411877949785 : (((p3 ∧ (p5 → (p5 ∧ (p2 → p5)))) → ((((p1 → ((p4 → (False ∨ p4)) ∨ True)) ∧ (p3 → p4)) ∨ p1) ∧ ((p1 ∧ True) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205843763630416732713555081657 : (((p2 → False) → ((p4 ∧ p1) ∨ False)) ∨ ((((p3 ∧ p4) ∨ (p2 → False)) ∧ ((p3 → (((False → p4) → (True ∧ p2)) → p1)) → p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790035849795932417529289459896 : (((p5 ∨ ((False ∨ p5) ∨ (((p1 → (p2 ∨ (p4 ∨ (p2 ∨ (p1 ∨ (p2 → p5)))))) ∨ False) ∨ (((p5 ∨ False) ∨ p5) → (True ∨ p2))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3438975463132146642836177474 : (True ∧ (((p2 ∨ ((p3 ∧ p2) → (p1 ∨ True))) → ((p1 ∨ p4) ∧ False)) ∨ (((p5 ∨ (True → (p5 → p3))) ∨ p3) → (False → False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160774314328530914985190675122 : (((p3 ∧ (p2 ∨ ((p2 → False) ∨ p4))) ∧ ((p5 ∨ (p4 ∧ ((p4 → (p5 ∧ p5)) ∧ True))) → False)) → (((p2 ∨ False) ∨ (True ∧ p4)) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147456877789122567331944872382 : ((((p2 ∨ False) → ((((True ∨ (p4 ∧ False)) ∧ p5) ∨ False) ∧ ((((p3 ∨ True) → p5) → p3) → p2))) ∨ p4) ∨ ((p4 ∨ p3) → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783795378927578803364808442269 : (((p3 ∨ (((p1 → p1) ∧ (p5 ∨ p3)) ∨ (p1 → ((((p3 ∨ (p5 → False)) → ((False → p1) → True)) ∧ p3) ∨ ((p5 → p3) → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330418764342099933242862077377 : (True → (p3 ∨ (((p3 ∧ ((True ∨ p3) → (p2 ∨ False))) ∨ (True ∨ ((((True → p2) ∨ p3) ∨ p4) ∨ (((p3 ∧ p4) ∧ p2) → True)))) ∨ p5))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136455783954753393650338061222 : (((p4 ∨ (False → (False → p5))) → ((False ∨ True) → (p3 ∧ ((p3 ∨ (((True ∨ p1) ∨ (p5 ∨ p1)) ∧ True)) → False)))) ∨ (p3 → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745501165189703590160917273367 : ((((True ∨ True) → (p5 ∨ (((((False ∨ p2) ∧ p1) ∨ (True ∨ ((p5 → ((p2 ∨ (p1 ∧ p2)) ∨ p2)) ∨ (p4 ∨ p3)))) ∨ True) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_487586685932221982642665551387 : (((((False ∧ ((p2 ∨ p1) ∧ p1)) → False) → ((p5 ∧ (((False ∨ ((p3 ∧ False) ∨ (p4 → p1))) → (p5 ∨ p4)) ∨ p2)) ∨ (p2 → True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230945218742211997747960658635 : (((p3 ∧ p4) ∨ p2) → (((p5 → (p2 ∨ (((False → p5) ∧ p2) ∨ p2))) → p5) ∨ ((((False ∧ p1) ∨ True) ∨ p5) ∨ (p1 ∨ (p4 ∨ p2))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
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
theorem thm_5_vars_157708897504327871750689131734 : (((((True ∧ (True → (p5 ∧ (p3 ∧ (True ∧ p5))))) ∧ False) → (True ∧ p3)) → ((True ∧ p4) ∧ False)) ∨ (True ∨ (False ∨ ((p2 ∧ p4) ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69229564675187609859991873783 : ((p5 → (((p3 ∨ (p4 ∧ p4)) ∨ p3) ∨ ((p5 ∨ p5) ∧ (p2 → ((((((p1 ∧ p3) → False) → p4) ∨ p1) ∧ True) → (p1 ∨ True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185537273612017510814620405246 : ((p3 ∨ (p1 ∧ (p1 ∧ ((p4 → p5) ∧ (False ∧ (True ∨ p5)))))) ∨ ((True → p4) → (True ∧ (((p5 → ((True ∧ p1) ∨ True)) ∧ p1) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4170937267379313186844117714 : (p4 ∨ ((p5 ∧ (p4 → (p4 ∧ (p4 ∧ (p3 → False))))) → ((((p4 ∧ ((p2 ∨ (p5 ∧ p4)) ∧ (p4 ∧ p3))) ∧ p4) ∨ False) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_774170123423562557960279284427 : (((False ∨ ((p3 ∧ ((p5 ∨ ((p2 ∧ (True ∧ (p4 ∧ p5))) ∨ ((p4 ∨ True) ∨ (True ∧ ((p1 ∧ p5) → p2))))) → p4)) → (True ∧ p4))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p5 ∨ ((p2 ∧ (True ∧ (p4 ∧ p5))) ∨ ((p4 ∨ True) ∨ (True ∧ ((p1 ∧ p5) → p2))))) := by
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
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134880106234820312160857641375 : (((p3 → ((((p1 → (False ∨ (False ∧ (p1 → False)))) → ((((p4 ∧ p5) → True) ∧ p1) → p3)) → p1) ∧ p2)) → p5) ∨ (p3 ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60535986281205735577985642417 : ((True ∧ ((((True ∧ True) → ((p1 → ((((p3 ∧ (p1 ∨ p4)) ∧ p4) ∧ p5) → False)) ∧ p2)) ∨ (p2 ∨ ((False ∧ p2) ∨ False))) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265042686367518670556054592994 : (True ∧ (True ∧ ((p2 → (p4 ∧ (p4 → (p1 ∧ (p2 ∧ ((p3 ∧ ((p3 ∧ p4) ∨ (p1 → True))) ∧ (p3 → p1))))))) ∨ ((p5 ∧ True) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_314860690754451722459131328438 : (p3 ∨ ((((p1 → (p3 ∧ (True ∧ p5))) ∨ (p4 ∧ True)) ∧ (p3 ∧ p4)) → ((False ∧ p5) ∨ (p2 ∨ ((p5 ∨ ((False → False) ∨ False)) ∨ p4))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302816382663408483968590627654 : (False ∨ (p5 ∨ ((p2 ∧ (p2 → (p4 → (((p5 ∧ (p4 → p4)) ∨ ((p1 ∨ p3) ∨ (p1 ∨ (True ∨ p2)))) → p1)))) ∨ ((True ∨ p3) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_119313164485347083331411882690 : ((p3 → (((True ∧ ((p2 ∧ p1) ∧ (p1 → ((p1 ∧ (p4 ∨ False)) ∧ (False ∨ (p3 ∨ p3)))))) ∧ p2) ∨ (True → (p3 ∨ True)))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18944701621965960359855421589 : (((p1 ∨ (p5 ∨ ((p2 ∧ p4) ∨ (True → ((p5 ∨ (((p1 → p1) ∧ p5) ∨ p5)) ∨ p3))))) ∨ ((((True ∧ p2) → True) → True) ∨ p5)) ∧ True) := by
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
theorem thm_5_vars_56475367311785821392319634392 : ((((False → p5) → (p1 ∧ p1)) → (p5 → (p4 ∨ ((((p1 → (p5 ∨ ((True → p2) ∨ p5))) → p5) ∨ (p4 ∨ (False ∧ True))) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47056770712710839892436870946 : (((((p5 ∧ (((p5 ∨ (((p2 → True) → p5) ∧ p2)) → p5) ∧ ((False → p5) → (False → p3)))) ∨ p1) ∨ (p1 ∧ p2)) ∨ (True ∨ p1)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160972507125428227341771426621 : (((p1 ∨ (p4 ∨ p1)) ∧ ((p2 ∧ (True ∨ (p1 ∧ (p3 ∧ p2)))) ∨ ((p1 → p1) ∨ (False ∨ False)))) → ((((p1 ∧ p1) → True) ∧ p3) ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- False on the left can always be used.
          apply False.elim h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- Conjunctions on the left can always be decomposed.
          let h28 := h27.left
          let h29 := h27.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h32 =>
          -- Disjunctions on the left can always be decomposed.
          cases h32
          case inl h33 =>
            -- False on the left can always be used.
            apply False.elim h33
          case inr h34 =>
            -- False on the left can always be used.
            apply False.elim h34
    case inr h35 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h36 =>
        -- Conjunctions on the left can always be decomposed.
        let h37 := h36.left
        let h38 := h36.right
        -- Disjunctions on the left can always be decomposed.
        cases h38
        case inl h39 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h40 =>
          -- Conjunctions on the left can always be decomposed.
          let h41 := h40.left
          let h42 := h40.right
          -- Conjunctions on the left can always be decomposed.
          let h43 := h42.left
          let h44 := h42.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h45 =>
        -- Disjunctions on the left can always be decomposed.
        cases h45
        case inl h46 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h47 =>
          -- Disjunctions on the left can always be decomposed.
          cases h47
          case inl h48 =>
            -- False on the left can always be used.
            apply False.elim h48
          case inr h49 =>
            -- False on the left can always be used.
            apply False.elim h49



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46815177788629771539490742655 : ((((((((p5 ∨ (p3 ∨ (p4 → (p3 → p1)))) ∧ (p2 → (((p2 ∨ p2) ∧ p3) → p3))) → p4) ∨ p2) → p3) ∧ False) ∨ (p5 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594631231739490339362828751885 : ((((((p3 → ((p2 ∧ (p3 ∧ p3)) ∧ (((False ∧ p5) ∧ (p5 ∧ p5)) ∧ True))) ∧ p4) → ((True ∨ ((p2 ∧ p4) → p1)) → p3)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351270645451650045819665635675 : (p4 → ((p5 → ((((True ∧ (True → (p3 ∧ (p2 ∧ p4)))) ∧ ((((p2 ∨ False) → p4) ∨ p3) ∧ p4)) ∧ True) → False)) ∨ ((p2 ∧ p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177939962832562297494627686212 : ((((True ∧ (p2 ∧ p1)) ∧ ((p5 ∨ ((p2 ∧ p5) ∧ True)) ∨ True)) ∨ p4) ∨ (p1 ∨ ((True ∨ (p4 → True)) → ((True → p3) → (True ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195189246501002610855421798427 : ((((p5 ∧ (p1 → p2)) ∨ True) ∨ (p3 ∨ True)) ∧ (((((True → p5) → p5) → False) → ((p4 ∨ p4) ∧ p3)) ∧ ((p2 ∧ (True → p4)) → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True → p5) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : ((True → p5) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h7
  -- False on the left can always be used.
  apply False.elim h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h12.left
  let h14 := h12.right
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_128173825588414808864501580566 : ((p2 → (p5 ∧ (p1 ∨ (((p3 → (p1 ∨ (p5 ∧ (p4 ∨ (p3 ∧ p1))))) ∧ ((p5 ∧ False) ∨ (p3 → (p3 → p5)))) → p2)))) → (p5 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52631167807542689274001892158 : ((((p5 ∨ p2) ∧ (p4 ∧ (p1 ∧ (((p3 → False) ∧ (p3 ∨ p3)) ∧ p1)))) ∨ ((((True ∧ (False ∧ False)) ∨ (p2 ∨ p4)) ∨ True) ∨ False)) ∨ p1) := by
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



