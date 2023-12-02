variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115362098620173910092592668634 : ((((p3 ∨ ((True ∧ (p2 ∨ p1)) ∧ True)) ∨ p4) ∧ ((((True ∨ p5) → False) ∨ (p4 ∧ (False → p2))) → ((p4 ∨ True) ∧ p4))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41152885053279412360081752479 : (((((True → False) ∨ (((p2 ∧ (p1 ∨ (p4 ∨ p5))) ∨ p4) → (p3 ∧ ((p2 → (True → p5)) ∨ True)))) ∨ ((p2 ∧ p1) ∨ True)) ∨ p3) ∨ False) := by
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
theorem thm_5_vars_344393499827531328953054966350 : (p2 → (p4 ∨ (p4 ∨ (((p1 ∨ (False ∨ (((p1 ∧ (p2 → (p5 ∧ (p2 ∧ (True → (p3 → p4)))))) ∧ p5) ∨ (p3 → True)))) ∨ p5) ∨ p2)))) := by
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
theorem thm_5_vars_50372394827643009293117630615 : (((((False → p4) → p1) → (p1 ∧ ((p1 ∨ (p5 ∧ False)) ∧ (((True ∨ p2) → False) ∧ (p5 → True))))) ∨ (p1 ∨ (p2 → (p2 ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48591106101116266054836075796 : (((((p1 ∨ (False ∧ p2)) ∧ ((p1 ∨ p4) ∧ ((p5 ∨ (True → True)) ∨ (p1 → (p3 ∧ p3))))) ∧ (p5 → False)) ∧ (p2 ∧ (p2 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304758154075604561780902291922 : (p1 ∨ ((True ∧ (((((p1 ∨ ((True → p4) ∨ p4)) ∨ (p5 ∧ p1)) ∨ p2) ∨ (p3 ∧ p2)) ∨ (((p2 ∧ p3) → p4) ∨ p3))) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145892148056219543051299222637 : (((True → p4) → ((p2 ∧ (p1 → p2)) → ((False ∨ (((True → (p1 ∧ (True → p5))) ∧ True) ∨ p2)) ∨ p2))) ∧ (p3 → ((p4 ∧ False) ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341982482087980883523865639248 : (p2 → (((((True ∨ True) → p2) → (((True ∨ (True ∨ p3)) → (True ∨ (False → p5))) ∧ (p2 ∨ True))) → (False ∧ p3)) ∨ (p1 → (p4 ∨ p1)))) := by
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
theorem thm_5_vars_259807779017168175983975598894 : ((p1 → p3) → ((((((p3 ∨ (((False ∨ (p4 ∨ False)) → ((p5 ∧ True) ∧ True)) → False)) ∧ (p4 → p5)) ∨ False) → p3) → False) ∨ (p1 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136762573833184218381410560199 : (((p3 ∨ p5) ∧ (((p1 ∧ False) ∨ (p4 → (((False → (True ∧ (p5 ∨ p3))) → (p5 ∧ p2)) ∧ p3))) ∨ (p2 ∨ p5))) ∨ ((False ∧ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119785811088068776353629844367 : (((((((p2 ∨ p1) ∧ ((True ∧ (p3 → (p1 ∨ ((p1 → ((p3 ∨ p5) → p1)) → p5)))) → False)) ∨ True) ∨ p4) → False) ∧ True) → (False ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((((p2 ∨ p1) ∧ ((True ∧ (p3 → (p1 ∨ ((p1 → ((p3 ∨ p5) → p1)) → p5)))) → False)) ∨ True) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : ((((p2 ∨ p1) ∧ ((True ∧ (p3 → (p1 ∨ ((p1 → ((p3 ∨ p5) → p1)) → p5)))) → False)) ∨ True) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184733083719809299742440338451 : (((((p1 ∧ p5) ∨ p1) ∧ True) ∧ (p1 → (p4 ∨ (p4 → p5)))) ∨ (p2 → ((p3 ∧ ((False ∧ ((p1 ∧ p3) → True)) ∧ p5)) ∨ (False → p2)))) := by
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
theorem thm_5_vars_209231980366880437200278559445 : ((p5 ∨ ((p2 ∧ (p3 ∧ p4)) ∨ True)) → ((False ∨ ((True → ((((False → p5) → p4) → (p1 ∧ p5)) ∧ p5)) → ((p1 ∨ True) ∨ True))) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
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
theorem thm_5_vars_178960423154262942360712050554 : (((p1 ∨ p2) ∨ ((p4 ∨ (p5 ∨ (p1 → (p4 ∧ (True ∧ p5))))) → p1)) ∨ (False → ((((p1 ∧ False) ∧ ((p4 → True) → p1)) → p1) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313945323722058952829383856938 : (p3 ∨ (((((p4 ∧ p2) ∧ ((True ∧ (((p1 ∨ p3) ∧ True) ∨ p5)) ∧ (False → False))) ∨ (((p2 ∧ p5) ∧ p2) → p4)) → p1) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302722297717852462338124387522 : (False ∨ (p3 ∨ (False ∨ ((((p5 → ((False ∧ (p5 ∨ p1)) → (False ∨ ((p5 ∨ p3) → False)))) ∧ True) ∧ (p5 ∧ (p1 → p3))) ∨ (True ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186829291681904035484887493045 : ((((p5 ∨ (p5 ∨ p1)) ∨ p1) ∨ (((False → False) ∧ p1) ∧ True)) → (True ∧ (((((p4 ∨ p5) → (p2 → p2)) → (p5 → p2)) ∧ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h7 =>
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
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263103261640402849272957132435 : (True ∧ ((((p4 → True) ∧ (p3 ∨ ((True ∧ (p2 ∧ p1)) ∧ (p2 ∧ ((p1 ∨ ((p3 → False) ∨ p2)) ∨ False))))) ∨ (p3 ∧ p2)) ∨ (False → p1))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57741414887842460862565389107 : ((((p5 ∨ p2) → p5) → (((p5 ∨ ((True ∨ (p5 ∨ p4)) → (p1 ∧ (p5 ∧ True)))) → p4) → ((((p3 ∨ p2) ∧ True) ∧ p2) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2659245597658765860095151005 : ((((p1 ∧ False) → p4) → (p3 ∨ p4)) ∨ (True ∨ (((p1 ∧ p5) ∧ True) ∨ (False ∨ ((p4 ∨ (False ∧ (True ∨ p5))) ∧ (p4 ∧ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254044608984625140852629143842 : ((p2 ∧ True) → (((((((p1 → (p3 ∨ (True ∧ p3))) ∨ p4) ∨ p1) → (p4 ∧ p1)) → (p3 ∨ p4)) ∧ p3) ∨ ((False ∧ (p5 → p2)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215149722752105294525535372640 : (((p5 → p5) → (False ∨ p1)) ∨ (False → (p5 → (((p1 ∧ p4) ∧ p1) ∨ (p4 → (p4 ∧ ((((True → False) → p5) → (p4 → False)) ∧ p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118236889406701625653125946135 : ((p1 ∨ ((p4 ∧ (p3 ∧ ((((p1 ∧ (((p4 → False) ∨ p3) → (p3 → True))) → (True ∧ (p5 → False))) ∧ p3) ∨ p1))) → p5)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50612625846070537993024926113 : (((((p3 → (p1 ∧ True)) ∨ (p2 → (False → ((p1 ∧ ((p1 ∨ p4) ∨ True)) ∧ p3)))) → (p1 ∧ True)) → (((False ∧ True) → p4) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168256138810218832824274778782 : (((False ∨ (True → False)) → ((((p5 ∧ p4) → p3) ∧ ((p3 ∨ (p2 ∨ p4)) ∧ p1)) → True)) → ((((False ∨ p4) ∧ True) → False) ∨ (True ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53710215201931666094863503658 : (((p2 ∨ (((p2 ∧ False) ∧ p2) ∧ ((p3 ∨ False) ∨ p5))) ∧ ((False ∧ (False ∧ (p5 → (p2 ∨ (((p1 ∧ False) ∧ p3) ∧ p5))))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40044888014602023809328274916 : (((((p5 ∨ (p2 ∧ ((p3 → ((True ∧ p3) → False)) ∨ ((((p4 ∧ p1) ∧ p3) ∧ p2) ∨ ((p1 ∨ p5) ∨ p5))))) ∧ p4) ∧ p4) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136061035837176875824881159307 : ((((p2 → (p3 ∧ (p1 ∧ (p5 ∨ False)))) → p5) ∧ (((p1 ∧ p5) ∧ p4) ∧ ((True ∨ (False ∧ False)) ∨ (p1 ∨ p2)))) ∨ ((p5 ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620763298523947205004061231198 : (((((p4 ∧ p3) → (((p1 → (p3 ∨ (((p3 ∨ ((True → p5) ∧ ((p5 ∧ True) ∧ (p2 → p5)))) → True) ∧ True))) ∨ p3) → False)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318476462631528453729644004201 : (p4 ∨ ((((((p4 ∨ p4) ∨ p1) ∨ ((p4 → (p2 ∧ False)) ∧ (p3 → True))) → p3) ∨ (False → (p5 ∧ (p2 → (True → True))))) ∧ (False ∨ True))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263985902444280738292088015617 : (True ∧ (((p5 → (p3 ∧ p5)) → (((p3 ∧ True) ∧ p2) ∨ (p3 ∨ p4))) ∨ (((((True → p5) ∧ (p5 ∨ (p3 ∧ p3))) ∧ p5) ∧ p3) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184224192953741328600926012095 : (((((True ∧ p4) → ((False ∨ p5) ∨ (p4 ∧ True))) ∨ p1) → False) ∨ (((((p2 → (p2 → True)) ∨ p2) → False) → p1) ∨ ((True → p3) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 → (p2 → True)) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111741940213135961386728002325 : ((((p1 ∨ (((((p2 ∧ True) ∧ p4) ∨ (p2 ∨ p2)) → p4) ∧ (True ∧ ((True ∨ ((p5 → p4) ∨ p2)) ∨ p2)))) → p3) ∨ True) ∨ (False ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215255470122354935737464946291 : ((False ∧ (p2 ∧ (p3 ∨ p4))) ∨ (p5 → ((p5 ∧ ((p3 ∨ (((((p3 ∨ False) ∧ p3) ∨ p4) ∨ (p2 ∨ p4)) → p5)) ∧ (p5 ∨ p4))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h8
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179634160456085535849399356487 : ((p4 → (True ∧ (((p3 ∧ (p3 ∧ p1)) ∨ ((p4 ∨ p5) → p1)) ∨ p4))) ∨ ((True ∨ ((p1 → (p3 ∨ (p1 ∧ p2))) ∨ (p2 ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305002091783510540889348057998 : (p1 ∨ ((((p5 ∧ (((((p1 → p3) → p3) → p1) ∧ True) ∨ (p3 ∨ p5))) → False) ∧ ((True ∧ (True ∨ p3)) ∧ True)) ∨ ((p5 ∨ True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316600599121757036976207474646 : (p3 ∨ (p3 ∨ (p4 → ((p4 → p5) → (((p5 ∨ p2) ∨ p1) → ((False ∧ (False ∧ (p3 ∧ ((p5 ∧ (True → p2)) → True)))) ∨ (p3 → True))))))) := by
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
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44844798797950531256953059536 : (((((p5 ∧ p4) → False) ∨ (p3 ∧ (p2 ∨ ((p5 → p5) ∧ ((((p2 ∨ p5) ∨ True) ∨ p5) ∨ ((p1 → p2) ∨ (p5 ∧ True))))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156964008249141059202516846584 : ((((p5 ∨ (p1 ∧ (((p1 → p4) ∨ (p2 ∧ (p4 ∧ p1))) ∨ p2))) → (p5 ∨ (p4 ∨ p5))) ∨ p2) ∨ (True ∨ (((p1 → p1) ∧ p5) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134035185578572871850209525877 : (((((((((True → (p1 → False)) → p2) ∨ (p3 ∨ p4)) ∧ False) ∧ p5) ∨ (((p4 ∨ p5) ∧ True) ∧ p3)) ∨ p5) ∨ True) ∨ ((True → p5) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52868272862911365623282193166 : (((p2 ∧ (p2 → (p1 ∧ (p1 → ((False ∧ (p3 → (p2 → p2))) ∧ p3))))) → (p3 ∨ ((((True ∧ (p2 ∨ p1)) → p5) ∨ p1) ∧ p1))) ∨ p1) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774254336990398615503805369101 : (((False ∨ (((p3 ∧ (False ∧ ((p2 ∧ p5) → p3))) ∨ (p1 ∧ ((p4 ∧ (p1 ∨ p5)) ∧ (p1 ∨ (p3 ∨ p1))))) ∨ (False ∧ (p1 ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358718153229587295518937847778 : (p5 → (p5 → ((p3 ∨ (p4 ∨ ((((((((p2 → True) → False) → p5) ∧ p3) ∧ p1) ∧ p4) ∨ p2) ∨ (True → p2)))) ∨ (False → (False → p3))))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256477815353337970413170713943 : ((False ∨ p4) → (((p1 → p1) → ((False ∨ p1) → ((p4 → (p4 ∨ (p3 ∧ p1))) ∧ True))) → (((p3 → p1) ∨ ((False ∨ False) → True)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321122383247942860120578328476 : (p4 ∨ (p2 ∨ (((((False → p4) → p5) ∧ ((False ∧ ((p5 ∨ p5) → p1)) → False)) ∨ (p3 ∧ (p1 ∨ ((p4 ∨ p4) ∨ False)))) ∨ (False ∨ True)))) := by
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
theorem thm_5_vars_41300572369658352073780589046 : ((((p5 ∨ ((((True ∧ p2) → p1) → (True → (((False ∧ p1) ∧ p4) ∧ (False → True)))) ∧ p1)) → ((p1 → p4) ∧ (False ∨ False))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230869053087690991747464067098 : (((p1 ∧ p4) ∨ p5) → ((p4 ∨ p2) ∨ ((((p1 ∧ p3) → (p1 ∨ p2)) ∨ ((p3 → p2) ∧ p2)) → (p4 → (False ∨ ((p3 ∨ p4) ∨ False)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133583260215655034530701891539 : (((((p1 → p2) ∨ (False ∧ (((p4 ∧ p2) ∨ p3) ∧ (True ∧ (p1 ∧ ((p4 ∨ (True ∨ p5)) ∧ True)))))) ∨ p1) ∧ p5) ∨ (True ∨ (p4 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646682670270140408843623384259 : ((((p2 → ((((p1 ∨ (p1 → (p2 → (p5 ∨ p3)))) → (p4 ∧ (False → ((p2 ∨ (True ∨ p1)) ∧ p4)))) → (p1 → p2)) ∧ p2)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225230240162208598106798358728 : (((p5 ∧ p3) ∧ False) ∨ (((True → ((p3 → True) → p4)) ∧ ((((p3 ∨ p1) ∧ (True ∨ (p3 ∧ p2))) ∧ True) ∨ (p4 → (False ∧ True)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753539685085741721425901149283 : (((False ∧ (((p2 ∧ p3) ∨ ((p1 → ((p4 ∧ ((p5 ∨ (p1 ∨ (p2 → p3))) → p2)) ∨ p4)) ∨ False)) ∨ (True → ((p4 → True) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669038639652229143936605839236 : ((((((p1 ∨ ((p4 ∧ ((p3 ∨ (False ∨ False)) ∧ False)) → ((p5 → p5) ∨ ((p4 ∨ p3) ∨ p2)))) ∨ p2) → p2) ∨ (p5 ∨ (p4 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212450609569786393516166447390 : ((p3 ∨ (True ∨ (p1 ∧ False))) ∧ ((p3 ∧ (p2 ∨ (False ∨ ((p5 → True) ∨ (p3 → ((p3 ∧ False) ∧ p5)))))) ∨ (p1 ∨ ((p2 ∧ p3) → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60374393534310345766168525847 : (((p3 → p1) → ((((p1 ∨ ((False ∨ p4) ∧ (p4 ∧ (p3 ∧ True)))) ∧ ((p2 ∨ p2) ∧ (p3 ∨ p2))) ∧ ((p2 ∧ p2) → p5)) → p5)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h12 : (p2 ∧ p2) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h10
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h13 := h4 h12
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h15 : (p2 ∧ p2) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h14
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h16 := h4 h15
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h18 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h19 : (p2 ∧ p2) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h17
          -- One of the premise coincides with the conclusion.
          exact h17
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h20 := h4 h19
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h21 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h22 : (p2 ∧ p2) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h21
          -- One of the premise coincides with the conclusion.
          exact h21
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h23 := h4 h22
        -- One of the premise coincides with the conclusion.
        exact h23
  case inr h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h27 =>
      -- False on the left can always be used.
      apply False.elim h27
    case inr h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h26.left
      let h30 := h26.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- Conjunctions on the left can always be decomposed.
      let h33 := h6.left
      let h34 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h35 =>
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h36 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h37 : (p2 ∧ p2) := by
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- One of the premise coincides with the conclusion.
            exact h35
            -- One of the premise coincides with the conclusion.
            exact h35
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h38 := h4 h37
          -- One of the premise coincides with the conclusion.
          exact h38
        case inr h39 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h40 : (p2 ∧ p2) := by
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- One of the premise coincides with the conclusion.
            exact h39
            -- One of the premise coincides with the conclusion.
            exact h39
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h41 := h4 h40
          -- One of the premise coincides with the conclusion.
          exact h41
      case inr h42 =>
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h43 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h44 : (p2 ∧ p2) := by
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- One of the premise coincides with the conclusion.
            exact h42
            -- One of the premise coincides with the conclusion.
            exact h42
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h45 := h4 h44
          -- One of the premise coincides with the conclusion.
          exact h45
        case inr h46 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h47 : (p2 ∧ p2) := by
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- One of the premise coincides with the conclusion.
            exact h46
            -- One of the premise coincides with the conclusion.
            exact h46
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h48 := h4 h47
          -- One of the premise coincides with the conclusion.
          exact h48



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50749011949662580361506122436 : (((p3 ∧ (((p3 → (p5 ∧ ((p1 ∨ p4) ∧ p2))) ∨ ((p4 ∨ p4) ∧ p3)) → (p4 ∨ (p3 → p2)))) → (p2 → ((p5 ∧ p3) ∨ p2))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674243505731137644207156000113 : ((((p5 ∧ (p4 → ((((True ∧ (p5 → p3)) → p2) ∧ (((p3 → p1) ∧ ((p2 → p3) ∨ p1)) → p2)) ∧ p2))) → (p3 ∨ (p4 → p4))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44528596694929279995499523100 : ((((((False → True) ∧ ((p1 ∧ p2) ∨ (p4 → p4))) ∧ p4) → ((((True ∧ (p5 ∧ (p3 ∨ p5))) ∧ False) ∨ (p3 → p5)) → p5)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116214625813997801491829478161 : ((((p4 ∧ False) ∨ p5) ∨ (p3 → ((((False ∧ (p2 ∨ ((p1 → p4) → p4))) ∨ ((p1 ∧ True) ∧ p2)) ∧ (p5 ∨ p5)) ∨ p3))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112082793983011754259837091444 : ((((False ∨ p2) ∨ (((p5 ∨ (p4 ∨ p1)) → (((p1 ∧ (True ∧ (p3 → False))) → (p2 → p5)) ∨ p5)) → (p4 ∧ p4))) ∨ p4) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213730578768338733157051490565 : ((((p4 ∨ p2) → False) ∨ False) ∨ ((p3 → (p2 ∧ ((False ∨ ((p3 ∧ ((False ∧ p1) ∧ p2)) → True)) ∨ (((p1 ∧ True) ∨ p2) → p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166447216077848521600315583782 : ((p2 ∨ ((False ∨ ((False ∨ ((p1 ∧ (True → (True → p2))) ∨ p2)) ∨ (False → p2))) → p1)) ∨ (False ∨ ((p5 ∧ (p2 → p4)) → (p1 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254423165010870078152289447562 : ((p2 ∧ p5) → ((p4 → (p2 ∧ p5)) → (((p5 → ((False ∧ (p5 → (p3 ∧ ((p1 ∧ True) ∧ ((p2 → p1) ∨ True))))) → p3)) → p3) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152641986610695424293417633170 : (((p5 ∨ p1) ∧ ((True ∧ (False → (((p3 ∧ (True ∨ ((p4 ∧ p3) ∧ True))) → p1) ∧ (p1 → p4)))) ∧ p1)) → ((p3 ∨ (p4 ∧ p4)) ∨ True)) := by
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
    let h7 := h5.left
    let h8 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257666432097170888775029246571 : ((p3 ∨ p3) → (((p4 ∨ (p5 ∨ (p2 ∧ ((p2 ∨ False) ∨ p2)))) ∨ ((p4 ∧ ((((p5 ∨ p1) → p4) → False) ∧ False)) ∨ (p3 ∨ p5))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172672515657767289071874791811 : (((p4 → True) ∧ ((((((p4 ∧ False) → (p2 ∧ False)) ∧ p2) ∨ p2) → False) ∨ p2)) ∨ (False → ((p1 ∨ ((p4 ∨ p5) ∨ (p5 ∧ p1))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741185773647961122596830687385 : ((((p4 ∨ p2) ∨ ((p4 ∧ (p3 ∧ (((p2 ∨ p4) ∨ (((True → ((True ∨ p4) ∧ False)) ∧ True) ∧ (True ∨ (True ∧ p3)))) ∨ p5))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791949637150678558864805633735 : (((True → ((p5 ∧ ((True ∧ ((False ∨ ((p5 ∨ (p5 ∧ p4)) ∨ p5)) ∧ ((True ∨ (p4 ∧ False)) ∨ p3))) ∨ (p2 → p1))) ∨ (True ∨ p4))) ∨ p3) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53807393220334914824453373829 : ((((p3 ∨ (p1 → ((p2 ∨ (p1 ∧ p3)) ∨ p4))) → p4) ∨ ((p4 ∨ (p5 ∨ (p1 ∨ p2))) → ((p4 → (True ∧ (p5 ∨ p4))) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165152311564410097096123441877 : ((((p4 → (p5 ∨ ((p3 → (p3 ∧ p4)) ∧ p1))) → (p5 ∧ (p3 ∧ p1))) ∧ (p5 → False)) ∨ (((p5 → (p2 ∨ (p2 → p5))) ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263544133491696768699499080962 : (True ∧ ((p2 → ((False ∨ (False ∨ (p1 → p5))) → (((p1 ∧ False) ∨ (p5 → (p1 ∨ (p4 ∨ p3)))) ∨ p2))) ∧ (((p4 ∧ False) → False) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190336135039966472671504290402 : (((((False ∨ p2) ∧ p1) ∧ ((p4 ∨ p5) ∨ p1)) ∨ True) ∨ (p3 → ((((p4 ∧ ((True → (p4 → p2)) → False)) ∨ True) ∨ p1) → (True ∧ p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354692191214788528973100723483 : (p5 → ((((True → (((p2 ∨ p4) ∨ p3) → (p4 ∧ (p1 ∨ False)))) ∨ ((p5 ∨ p5) → (False ∧ ((False ∨ p2) → False)))) ∨ (False → p1)) ∨ p2)) := by
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
theorem thm_5_vars_722988681629515777882236907937 : (((((True ∨ p5) ∨ p3) ∧ (p1 ∨ ((((p4 → (True ∨ ((p2 ∧ (p4 ∧ (False ∨ p2))) → (p1 → p1)))) ∧ p3) → p1) ∨ (p3 ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617491239679143846037550756864 : (((((((p1 ∧ False) ∨ (p4 ∧ p2)) → p4) ∧ ((((True → ((p5 ∧ True) ∨ (False ∨ False))) ∧ p2) → (False ∧ (p2 → p1))) → p2)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205666658541252142977455091056 : (((p1 ∨ p4) ∨ ((p2 ∧ p4) ∨ False)) ∨ ((((p3 → (p2 → p5)) ∨ ((((p1 ∨ p4) ∧ False) → True) ∨ (p5 ∨ p2))) ∨ p1) → (True ∨ p5))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h8 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228531809901085730232588635226 : ((p1 ∨ (p2 ∧ p1)) ∨ (((False ∨ ((p4 ∧ (False ∨ p1)) ∧ (True ∨ True))) ∧ (p2 ∨ ((p3 ∧ (((False → True) → p1) → p4)) ∧ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317980233231835110945466157331 : (p4 ∨ ((p2 → (p2 ∧ ((((p1 → True) → (p4 ∧ False)) ∧ p2) → (((p5 ∧ p5) ∨ p1) ∨ ((p4 ∨ p5) ∧ (p5 ∨ (p5 → p3))))))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p1 → True) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h5
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760133562306355237867539906086 : (((p2 ∧ (((p3 ∧ p1) ∨ p4) → (p3 ∧ ((p4 ∨ (p3 → ((False ∧ (((False ∧ p3) → p3) ∧ p2)) → ((p4 → False) → p1)))) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631584024895871423370685921594 : (((((((((True ∨ p5) → False) ∨ ((p2 ∧ (((False ∧ p3) ∨ p4) ∨ p1)) ∨ p2)) ∧ True) ∧ (((p5 → p1) ∨ p5) ∨ p5)) → True) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800320217872731665063058260877 : (((p2 → (((((p2 ∨ (p2 ∨ False)) ∨ p5) → (p2 → ((True ∧ p3) → p2))) → (p5 ∧ ((((p2 ∨ p2) ∧ False) → p5) ∧ p4))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741438347285720882281773943892 : ((((p5 ∨ p1) ∨ ((False ∨ False) ∨ ((True ∧ (False → p1)) → ((p2 ∨ ((p3 ∧ p3) → (((False ∧ p1) → p1) ∨ True))) → (True → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617796380199081724296052618214 : ((((((((True ∧ True) → p1) ∨ p3) ∧ p1) → (p2 ∨ (p2 ∧ (((p1 ∧ (False ∨ p2)) ∧ (p1 ∧ (True ∧ (p2 ∨ p1)))) → p4)))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353544261719787371788817271138 : (p4 → (p3 ∨ ((((False ∨ (((False ∨ (False ∧ ((p5 ∨ p4) ∨ (True ∧ p3)))) → p3) → (p4 → p5))) → p2) → (True ∧ p3)) ∨ (p2 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117129821427222951294362030504 : (((p4 → p4) → ((False ∧ (True ∧ (((((p1 → (p4 ∨ p4)) → p2) → p3) → p4) → p4))) ∨ (False → ((p3 ∧ True) → p1)))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179568468362750945374319756130 : ((p2 → ((p5 → (p4 ∨ ((p4 → False) ∧ p3))) ∨ (p4 ∨ (p3 → p5)))) ∨ (((p2 → ((True → p3) → p2)) ∧ (False → p4)) ∧ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311846973827557253278582672053 : (p2 ∨ (p1 ∨ (False ∨ (((p1 → ((p1 → (p2 ∨ p3)) ∨ p3)) → ((((p2 → p2) ∨ p2) ∧ p4) ∨ (False → False))) ∧ (p1 ∨ (True ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234315090327205197549912359503 : ((p1 → (p1 ∧ p4)) → ((p2 → (p4 ∨ (((False ∨ p2) ∨ p2) ∧ True))) ∧ (p5 ∨ (p4 → (True ∧ (((p5 ∨ p2) ∨ (p4 ∧ p4)) ∧ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46872742278653145902023174996 : ((((p1 → (p3 → (((False ∧ (p2 ∧ (((((p2 ∧ True) ∨ p2) ∧ p5) ∨ p3) → p4))) ∨ p4) ∨ (p5 ∧ p5)))) ∧ p1) ∨ (p4 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174858655412291955082262753512 : (((p4 ∨ p3) ∨ (((p4 → (p4 ∧ p1)) ∧ p5) ∧ (((p3 ∨ p4) ∧ False) → False))) → (((p1 ∧ True) ∨ False) → (p1 ∨ ((False ∧ False) ∧ False)))) := by
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
    cases h1
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114054063255423245728879164095 : (((((p1 ∨ ((p3 ∧ True) → ((p3 ∨ (p2 ∨ p1)) → p4))) → (True ∨ True)) → (p2 ∨ (p1 ∧ False))) ∨ ((True ∨ p5) ∨ p1)) ∨ (p4 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41009515948454871477337947934 : (((((p2 → (True ∧ ((True ∨ (((p5 → ((False → False) ∨ (p3 → p4))) ∨ (True ∨ p2)) ∨ False)) → True))) ∧ True) → (p4 ∨ p5)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204885893365182550679639857467 : ((((p5 → (p1 ∨ p1)) → p2) → p1) ∨ ((((p2 → p5) ∨ (p1 ∧ True)) ∨ (((p3 ∧ (True ∧ p3)) ∧ (False ∨ p5)) → (False ∨ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146959115729431510302159264668 : ((((p3 ∨ ((p4 ∧ (p3 ∧ p3)) ∨ (False ∨ (p3 ∧ (p3 → (((p4 → True) ∨ p5) ∧ p4)))))) ∨ p3) ∧ False) ∨ (p5 → (p1 → (p5 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201016649171138116596214078431 : ((p3 ∨ (p3 → (False → ((False ∨ p2) → p4)))) → (((p1 → ((p1 ∨ False) ∨ (p1 ∨ (True ∨ (p4 ∧ p1))))) ∧ (p1 → (p3 ∧ False))) ∨ True)) := by
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
theorem thm_5_vars_46158559543694774625818246143 : ((((((p1 ∨ (p1 → (p1 → True))) ∧ (((p4 ∧ p5) ∧ True) ∨ (False ∧ (False ∧ p2)))) → (False → (p1 ∧ p2))) → p3) ∧ (True ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310309625831977076845122214812 : (p2 ∨ ((p2 ∧ ((p4 ∨ p3) → (((True ∧ False) ∨ False) ∧ False))) ∨ ((((p4 → ((((p5 ∧ p1) ∨ False) ∨ True) ∨ p3)) ∨ p5) ∨ p1) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241482848113310298843985888354 : ((False → p2) ∧ ((((p5 → p3) → (p3 ∧ p4)) → p4) → ((p2 ∧ p3) → ((p4 ∧ (((False ∨ (True → True)) → p1) ∨ p2)) → (p2 ∨ p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h3.left
    let h12 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_559449851524790553579353089107 : (((p4 ∨ ((((True → (p5 → p5)) ∧ p3) ∧ (((p4 → True) ∧ p1) → ((False ∧ (p3 ∨ p3)) ∨ (p1 ∧ (False ∨ p1))))) ∨ (False ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193815463041041690928272543672 : ((p5 ∧ ((((False ∨ False) ∨ p1) ∧ p5) ∨ (p4 ∨ p5))) → (False ∨ (p2 → ((p3 ∨ (((p3 ∨ False) → (p5 ∨ (p4 ∧ p1))) ∧ p5)) ∧ True)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h12
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
      -- One of the premise coincides with the conclusion.
      exact h6
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h18
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h20 =>
        -- False on the left can always be used.
        apply False.elim h20
      -- One of the premise coincides with the conclusion.
      exact h2
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h23
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h25 =>
        -- False on the left can always be used.
        apply False.elim h25
      -- One of the premise coincides with the conclusion.
      exact h21
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250952406926562171551396527044 : ((p1 → p4) ∨ ((p5 → ((p5 → ((p4 ∨ (p3 ∨ False)) → False)) ∨ (p1 ∧ p2))) ∨ (((p3 ∧ True) ∧ p2) → ((p1 ∨ True) ∨ (p5 ∨ p3))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



