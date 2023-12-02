variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765097153572362184355175049663 : (((p4 ∧ ((p4 ∨ (((False ∨ p2) ∧ (False ∧ p4)) ∧ ((p1 ∧ (p3 ∨ (((p4 ∨ (False ∧ True)) ∨ False) ∧ p4))) ∧ p4))) ∧ (p1 ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59286949044021909882716147005 : (((p3 ∨ p3) ∨ (False ∨ ((p5 → (p3 ∧ ((True ∧ (True → (True → p3))) ∨ False))) ∧ (True ∨ ((((False → p1) ∨ False) ∧ p3) ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49095426442342776643941016599 : (((((p3 ∧ (p1 ∨ p4)) ∧ ((p5 → ((p4 ∨ (p3 ∧ (p5 → p3))) ∧ False)) ∨ True)) ∨ (p2 ∧ (p1 ∧ p4))) ∨ (False → (p2 → False))) ∨ p4) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127728713371577905470361318029 : ((True → ((((True → ((((p3 → p5) → p1) ∨ False) → True)) ∨ (False ∨ p2)) ∧ ((p2 → False) ∧ (p5 → (p5 ∨ p5)))) ∧ p4)) → (p4 ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206810089558551039075396848708 : ((p5 → (((p1 → False) ∨ p1) ∨ p2)) ∨ (((((p4 ∨ (((p2 ∨ p4) ∧ p5) ∨ p1)) ∨ (True ∨ True)) ∧ True) ∨ (p2 ∧ (p3 ∧ p5))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764752060345978588544938364017 : (((p4 ∧ ((p5 → ((p3 ∨ p1) ∨ (((p2 → (((p3 ∧ True) → p3) ∨ (p5 → p4))) ∧ ((p2 ∨ False) ∧ p3)) ∨ (p1 ∨ p4)))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337365530707215095571089202196 : (p1 → ((((False ∧ (False ∨ (((p4 ∧ p1) ∧ True) ∨ (p2 → p4)))) ∧ False) ∧ ((((p2 ∧ p4) ∨ True) → p4) → p3)) ∨ ((p1 → p1) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244394886211022004259257334305 : ((False ∧ p1) ∨ ((p5 → ((True ∨ (((p3 ∧ p4) → p4) ∨ p5)) → False)) ∨ (p4 → (False → ((p4 → (p2 → True)) ∧ (p2 ∧ (True → True))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116559833013659466954847921632 : (((p2 ∨ True) ∧ (((((p2 → (((p5 ∧ (True ∨ p4)) → False) ∨ True)) ∨ p1) ∨ p2) ∨ p4) ∧ (((False ∧ p4) ∧ False) ∧ p2))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201265165769513874858667198098 : ((p3 → ((True ∨ p5) → ((p3 → p3) ∨ p4))) → ((((p3 → ((p1 → p4) ∨ p2)) ∨ (p4 ∨ (True ∧ ((p1 → False) → True)))) ∨ p2) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206842735427434205564330279948 : ((p5 → (True → ((p2 ∨ p2) ∨ p4))) ∨ ((((((p3 → True) ∨ True) ∧ p3) ∧ (p1 ∨ p5)) → (p1 ∨ True)) ∨ ((p5 ∨ (p5 → p5)) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    cases h3
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264156472259684452745785181491 : (True ∧ (((p2 → (((p3 ∧ p1) ∨ p4) ∧ p5)) ∨ False) ∨ (((p4 ∧ p4) ∧ p5) ∨ ((p3 ∨ (False ∧ (p2 → ((False ∧ False) ∧ p3)))) → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_65685844141081316969012361053 : ((p4 ∨ (((p4 ∨ p1) ∧ ((True → p2) → (False ∧ ((True → p3) → ((((p2 → p2) ∨ False) → False) ∨ ((p5 ∧ p1) ∧ p4)))))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166476483025339021919636486027 : ((p3 ∨ ((False ∨ (((True ∧ (False ∨ False)) ∨ (((p3 → p3) ∨ p5) ∧ p2)) ∨ p5)) ∨ True)) ∨ (((False → p5) ∨ (p3 ∨ p5)) ∨ (p1 → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681537325155924316552526182738 : ((((False → (((((True ∧ (p3 ∧ False)) ∧ p1) → (True ∨ ((False ∧ p1) → p1))) → (p2 → p5)) ∧ True)) → (p3 → ((p3 ∨ p3) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133905088218720881162811105446 : (((p2 ∨ (((p3 ∧ (p3 ∧ ((p5 ∨ p5) → (p3 ∧ (p5 → (True ∨ ((True ∨ p3) → p5))))))) → False) ∨ p2)) ∧ p5) ∨ ((p3 ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3370784196048340116970926376 : ((True → False) → ((((((p3 ∨ p3) → (p3 ∧ (p2 ∨ ((p4 ∧ p1) ∧ (False ∧ ((p5 ∨ True) → False)))))) ∧ True) ∧ p2) ∧ True) ∨ p3)) := by
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
theorem thm_5_vars_733676829306025981760382954907 : ((((p5 ∧ False) ∧ ((False ∧ (((p1 ∨ p4) ∧ ((p3 ∧ True) ∨ False)) ∧ True)) ∧ ((p1 ∧ (p4 → ((True ∨ p2) ∨ p1))) → (p1 ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116133754308213657047002592090 : (((p2 ∧ (p1 → p4)) ∧ (((p2 → ((((((p3 ∨ (p4 → p2)) ∧ (p3 → p4)) ∨ p5) ∧ p3) ∨ p5) → False)) ∨ False) → False)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40080717601183767367344585477 : (((((((((True → True) ∧ (p3 → p3)) ∧ (p5 ∨ p3)) → ((p5 → (p5 ∧ p4)) → (p1 → p3))) ∧ (p1 ∧ p1)) → False) ∧ p2) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118556019114615560355972906795 : ((p3 ∨ (p3 → (((p1 → p1) → ((p2 ∨ (True → (p4 → (((False → p4) → p2) → (p1 ∨ (False → p1)))))) → p4)) → False))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244826688605637994555369770120 : ((p1 ∧ p1) ∨ ((p4 ∧ (p3 ∧ False)) ∨ (((p2 ∨ (p2 ∨ (p3 ∨ ((False ∧ True) ∨ ((p5 ∨ p5) ∨ (p4 ∨ p1)))))) ∨ False) ∨ (p5 → p5)))) := by
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
theorem thm_5_vars_252411371307719112250933875776 : ((p5 → False) ∨ (((p2 ∧ (p5 ∧ ((p3 ∨ p5) ∨ True))) ∨ (False ∧ p2)) → ((False ∨ (((p3 → True) ∧ p1) ∨ False)) ∨ ((p5 ∨ False) ∨ p1)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310837502779446793909334695830 : (p2 ∨ (((False → p1) ∧ p2) → (True ∧ (((p4 ∨ (p4 ∧ (p5 → p5))) → (((True ∧ p4) ∧ (p3 ∧ True)) ∧ p1)) → (p2 → (p4 → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : (p4 ∨ (p4 ∧ (p5 → p5))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h7
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51193410828665067716741453949 : ((((((p4 → (p2 ∧ p2)) → (p3 ∧ True)) → ((p1 → p3) ∧ False)) → (p1 → (p4 ∨ p5))) ∨ (True ∨ (((p2 → p4) ∧ p4) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57334723769271749415099730865 : (((p1 ∧ (p5 ∨ True)) ∨ ((((((p1 → p1) ∨ (False → ((True ∨ (p4 → p5)) → (p1 ∧ p1)))) → (p4 → p2)) ∨ True) ∨ p4) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51478764301998584050070325480 : (((((True ∨ p3) → (p5 ∨ (p5 ∧ p3))) ∧ ((True ∧ ((p3 ∧ True) ∨ (False ∧ False))) → True)) → (p2 → (p2 → ((p2 → p3) ∨ True)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57050408635023343023055305797 : (((p3 → (p2 → False)) ∧ (p3 → (((True ∨ p2) → False) ∨ ((((p5 → p3) ∨ False) → (p2 ∧ p3)) ∧ (((p1 ∨ False) ∧ p4) → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140145015750689834283380244564 : ((((((p3 ∨ (p4 ∨ (p4 → ((True → (p1 ∨ (p4 → p3))) ∧ (True ∨ p2))))) ∨ p3) ∧ p3) → p3) → (p3 ∧ p1)) → ((p1 → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55211589863168303611851981939 : ((((p1 → (p4 ∧ False)) ∧ (p5 ∨ p5)) ∨ ((p5 ∨ p3) ∧ ((False ∨ True) → ((((((p4 ∧ p1) ∧ False) ∨ p2) ∨ p3) ∨ p3) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56864227455677819101563979641 : (((False ∧ (p4 → p2)) ∧ (True ∧ (((((p5 ∧ False) ∨ False) ∨ ((p1 ∨ p1) ∧ ((p1 ∧ p3) → (p2 → p3)))) ∧ False) ∨ (p5 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231719677673504946322947815630 : (((p2 ∧ p2) → False) → ((p2 ∧ (False → (p4 ∨ p4))) → (((p4 ∨ (p3 ∨ ((False ∧ p4) → False))) ∨ ((p1 → (True ∧ True)) ∨ p5)) → False))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h2.left
      let h7 := h2.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h8 : (p2 ∧ p2) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h6
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h9 := h1 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h2.left
        let h13 := h2.right
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h14 : (p2 ∧ p2) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h12
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h15 := h1 h14
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h2.left
        let h18 := h2.right
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h19 : (p2 ∧ p2) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h17
          -- One of the premise coincides with the conclusion.
          exact h17
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h20 := h1 h19
        -- False on the left can always be used.
        apply False.elim h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h2.left
      let h24 := h2.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h25 : (p2 ∧ p2) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h23
        -- One of the premise coincides with the conclusion.
        exact h23
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h26 := h1 h25
      -- False on the left can always be used.
      apply False.elim h26
    case inr h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h2.left
      let h29 := h2.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h30 : (p2 ∧ p2) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h28
        -- One of the premise coincides with the conclusion.
        exact h28
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h31 := h1 h30
      -- False on the left can always be used.
      apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165141227261647459971693605622 : ((((p2 ∨ ((p5 → p5) ∨ (p4 → ((p2 ∨ p4) ∧ (False ∨ p5))))) → p2) ∧ (p3 ∨ True)) ∨ ((p5 ∨ (True ∨ (p3 ∨ False))) ∨ (True ∧ p1))) := by
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
theorem thm_5_vars_58958403724637611013195951848 : (((p2 ∧ p1) ∨ ((((p4 ∧ (p1 ∨ ((p2 ∨ (True ∧ p5)) → (True ∧ (p2 ∨ p5))))) ∧ p4) ∨ True) ∧ ((p1 → True) → (p2 ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656142848396050156808750286455 : (((((p5 → (True → ((((p2 ∨ p1) ∧ p2) ∨ ((p3 → p1) → p4)) → p1))) ∧ (p2 ∨ (p5 → (p2 ∧ (p1 ∨ p4))))) ∨ (p4 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255692043631800568474071853378 : ((p5 ∧ p5) → (((p4 ∨ ((p2 ∧ p4) → (p5 ∨ p5))) ∨ p4) → (p2 ∨ (((p2 → p3) ∧ p1) ∨ (((False → (False ∧ p3)) ∨ False) ∧ p5))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h7
      -- False on the left can always be used.
      apply False.elim h7
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h1.left
      let h10 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h11
      -- False on the left can always be used.
      apply False.elim h11
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h15
    -- False on the left can always be used.
    apply False.elim h15
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171685025085016836808505408071 : (((p3 ∨ (p5 ∨ (True → (p2 ∧ ((p2 ∨ p1) → (False ∧ (False ∧ False))))))) ∨ True) ∨ (p1 ∧ ((((False ∨ False) ∨ p3) ∨ True) → (p3 ∧ p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262726516600899034948749732998 : (True ∧ (((((((p5 → (p2 → p1)) → p3) ∧ p5) ∧ p4) → (False ∧ p4)) ∧ ((p1 ∧ True) ∧ (((p2 ∨ (p5 ∧ p5)) → p4) → True))) → p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174708006162117483937670189350 : (((p1 ∨ (p2 ∧ True)) ∨ ((p3 ∨ (True ∧ ((False ∧ (False → p1)) ∧ p5))) ∨ p3)) → ((True → False) → ((False ∧ (p3 ∧ p5)) ∧ (p2 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h5 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h6 := h2 h5
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h10
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h15 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h16 := h2 h15
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Conjunctions on the left can always be decomposed.
        let h22 := h20.left
        let h23 := h20.right
        -- False on the left can always be used.
        apply False.elim h22
    case inr h24 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h25 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h26 := h2 h25
      -- False on the left can always be used.
      apply False.elim h26
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h29 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h30 := h2 h29
      -- False on the left can always be used.
      apply False.elim h30
    case inr h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h34 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h35 := h2 h34
      -- False on the left can always be used.
      apply False.elim h35
  case inr h36 =>
    -- Disjunctions on the left can always be decomposed.
    cases h36
    case inl h37 =>
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h38 =>
        -- One of the premise coincides with the conclusion.
        exact h38
      case inr h39 =>
        -- Conjunctions on the left can always be decomposed.
        let h40 := h39.left
        let h41 := h39.right
        -- Conjunctions on the left can always be decomposed.
        let h42 := h41.left
        let h43 := h41.right
        -- Conjunctions on the left can always be decomposed.
        let h44 := h42.left
        let h45 := h42.right
        -- False on the left can always be used.
        apply False.elim h44
    case inr h46 =>
      -- One of the premise coincides with the conclusion.
      exact h46
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h47 =>
    -- Disjunctions on the left can always be decomposed.
    cases h47
    case inl h48 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h49 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h50 := h2 h49
      -- False on the left can always be used.
      apply False.elim h50
    case inr h51 =>
      -- Conjunctions on the left can always be decomposed.
      let h52 := h51.left
      let h53 := h51.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h54 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h55 := h2 h54
      -- False on the left can always be used.
      apply False.elim h55
  case inr h56 =>
    -- Disjunctions on the left can always be decomposed.
    cases h56
    case inl h57 =>
      -- Disjunctions on the left can always be decomposed.
      cases h57
      case inl h58 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h59 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h60 := h2 h59
        -- False on the left can always be used.
        apply False.elim h60
      case inr h61 =>
        -- Conjunctions on the left can always be decomposed.
        let h62 := h61.left
        let h63 := h61.right
        -- Conjunctions on the left can always be decomposed.
        let h64 := h63.left
        let h65 := h63.right
        -- Conjunctions on the left can always be decomposed.
        let h66 := h64.left
        let h67 := h64.right
        -- False on the left can always be used.
        apply False.elim h66
    case inr h68 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h69 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h70 := h2 h69
      -- False on the left can always be used.
      apply False.elim h70
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h71 =>
    -- Disjunctions on the left can always be decomposed.
    cases h71
    case inl h72 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h73 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h74 := h2 h73
      -- False on the left can always be used.
      apply False.elim h74
    case inr h75 =>
      -- Conjunctions on the left can always be decomposed.
      let h76 := h75.left
      let h77 := h75.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h76
  case inr h78 =>
    -- Disjunctions on the left can always be decomposed.
    cases h78
    case inl h79 =>
      -- Disjunctions on the left can always be decomposed.
      cases h79
      case inl h80 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h81 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h82 := h2 h81
        -- False on the left can always be used.
        apply False.elim h82
      case inr h83 =>
        -- Conjunctions on the left can always be decomposed.
        let h84 := h83.left
        let h85 := h83.right
        -- Conjunctions on the left can always be decomposed.
        let h86 := h85.left
        let h87 := h85.right
        -- Conjunctions on the left can always be decomposed.
        let h88 := h86.left
        let h89 := h86.right
        -- False on the left can always be used.
        apply False.elim h88
    case inr h90 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h91 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h92 := h2 h91
      -- False on the left can always be used.
      apply False.elim h92



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136873545144258381314841691955 : (((False ∨ p4) ∨ ((((False ∨ p2) ∨ ((False → (p5 → (True ∨ (p3 ∨ False)))) ∨ (p3 → p5))) ∧ (False ∧ p5)) ∧ p2)) ∨ (p3 ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111962051593685281878834099918 : ((((((True ∨ p4) ∧ False) ∨ ((p3 → p1) → p4)) → ((True → (True ∧ p4)) → (p4 ∧ (((p3 → p1) ∨ p2) → p3)))) ∨ p5) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113245851764863304076127878326 : ((((p3 ∧ ((((True ∨ (p1 → (p2 ∨ ((p1 ∧ p4) → p3)))) ∧ p3) → p3) → (p4 → p3))) ∧ (p4 ∧ p2)) ∧ (p1 ∧ p4)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309789977670554036801359827014 : (p2 ∨ (((p3 → ((False ∨ (p4 ∧ ((p3 ∨ p4) ∨ (p2 ∧ p5)))) ∧ (((p3 → p3) ∨ False) ∨ p4))) → p4) ∨ (((p3 → p3) → True) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200002228273609429309597299243 : (((((p2 → p1) → p1) → p4) → (p3 ∨ p3)) → (((False → (((p1 → False) ∨ (p5 ∨ False)) ∧ p5)) ∧ ((p3 → True) → (p5 ∧ p3))) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p3 → True) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63933044076550401702910789226 : ((False ∨ (((p1 ∧ ((((p2 → False) → (p2 → (p4 ∨ (((p5 → (p4 ∨ p4)) → True) ∧ p1)))) → p1) ∨ False)) ∨ (True ∨ p2)) ∨ p2)) ∨ p5) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157574663028406765390892385654 : ((((True ∧ p1) ∧ ((p4 → (((False → False) ∧ p4) → ((p3 → p1) → p1))) ∧ p1)) → (p4 ∧ p2)) ∨ (True ∨ ((p2 ∧ (p2 ∧ p2)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157500657892850794978394898193 : ((((p1 → p3) ∧ (((True ∧ ((p4 ∨ p1) ∧ (True ∨ p1))) ∨ p2) → (p2 ∨ p3))) ∨ (p5 → False)) ∨ (True ∨ (p4 ∧ ((p3 ∨ p3) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39602896203281215082108809265 : (((p2 ∨ ((((((p5 → ((p4 → p2) ∧ ((True → True) → (p2 ∧ False)))) ∧ p5) → p3) ∨ p5) ∨ p5) ∧ (False ∨ (p4 → p2)))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78735974372422867192460014369 : (((((p4 ∨ False) → ((p4 ∨ (p3 → True)) → ((p5 → p3) → p3))) → (p1 ∧ ((p3 ∧ ((p3 ∧ False) ∨ p2)) ∧ p2))) ∧ (p1 ∧ p3)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : ((p4 ∨ False) → ((p4 ∨ (p3 → True)) → ((p5 → p3) → p3))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h15 =>
        -- False on the left can always be used.
        apply False.elim h15
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h16 := h2 h6
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- We need to get the right conjuct of h17 based on <expert-advice>.
  let h18 := h17.right
  -- One of the premise coincides with the conclusion.
  exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115045171050407792712529794915 : ((((False ∨ ((p1 → p1) ∧ ((False → (p2 ∨ p4)) ∧ p2))) ∨ p4) ∨ ((p2 ∨ False) ∧ ((False → (p4 ∨ p5)) ∨ (True ∧ True)))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37682446431346144710440020142 : ((((((((True ∨ (p3 → p5)) → (p1 ∨ p2)) ∧ ((((p2 ∧ p5) → (p1 ∨ False)) ∧ p3) → False)) ∨ False) ∨ (p5 ∨ p1)) → p5) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355594255060729347696044836923 : (p5 → ((((p4 → (p4 → p5)) → False) ∨ ((p2 ∧ ((((True → p1) → (True → False)) ∨ (p5 ∧ (False ∧ p1))) → p4)) ∧ False)) ∨ (p3 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168200878828204974223711657925 : ((((p5 → p1) ∨ p3) ∨ ((p5 ∨ ((p1 → False) → ((True ∧ p2) ∧ (p5 ∨ p3)))) → p4)) → ((p4 ∨ p5) ∨ (True ∧ (p1 ∨ (True ∨ p2))))) := by
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231986408929631995029639701676 : (((p2 ∨ False) → p3) → ((p4 ∧ (p5 ∨ p3)) → (p5 → (p2 → (((False ∧ False) ∧ (((p1 ∧ (p3 → p1)) ∧ p2) ∧ p2)) ∨ (False ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144037085130946173702813807250 : (((p2 ∨ ((False ∧ p4) ∧ (((p4 ∨ ((((False ∨ p2) ∨ (p4 ∧ p3)) → p4) → False)) ∨ p5) ∧ p2))) ∨ True) ∧ (p3 → (p5 ∨ (False → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312141187897453578708812877662 : (p2 ∨ (True → ((p4 ∧ p4) ∨ ((p2 ∨ p4) → (True ∧ (True ∧ (False ∨ (((((p5 → (p1 → True)) ∧ p3) ∨ (p4 → p4)) → p3) ∨ True)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_427579797096781122840553860255 : ((((((((p5 → (((p2 ∧ ((p4 → p5) ∧ p1)) ∨ True) ∨ p4)) → (p2 ∧ (p5 → (p5 → p1)))) ∨ False) ∧ p2) ∨ p3) ∨ (False ∨ True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_302030701667624989298474247495 : (False ∨ (True ∧ ((((True ∨ False) ∨ (False ∨ p4)) → ((p1 ∨ False) ∧ (False → (p3 → (p2 → False))))) ∨ (p2 → (p2 → (p1 → (True → True))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232400666936780485193455325275 : (((p5 → p4) → p1) → ((p2 ∨ (((p1 ∨ (p5 ∨ (False → (False ∨ (p4 ∨ False))))) ∧ (((p2 ∨ p2) → True) ∨ False)) → p4)) ∨ (True ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156977274707212738425957479624 : ((((p1 ∨ (False ∨ (p1 ∧ (True → (p5 ∧ True))))) ∧ (((False ∨ p4) ∧ (p4 → p1)) → p3)) ∨ False) ∨ ((((p4 → p2) ∨ p1) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346818759295332963044793246817 : (p3 → ((((((p4 ∧ (p2 → False)) ∨ (p3 ∨ True)) → (p5 ∧ p2)) ∨ ((p4 ∧ p4) → (True ∨ p3))) → False) → ((False → p4) ∧ (True ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((((p4 ∧ (p2 → False)) ∨ (p3 ∨ True)) → (p5 ∧ p2)) ∨ ((p4 ∧ p4) → (True ∨ p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h4
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265831944991970253997247147110 : (True ∧ (p5 ∨ (((p2 ∨ p5) → ((((p4 ∨ ((p5 → p2) ∨ p5)) ∧ p5) → (p1 ∨ ((p3 ∨ p5) ∨ p2))) ∧ p1)) ∨ (p4 → (p1 → p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110858931726263992863403740351 : ((((((((((p1 → p1) ∧ (p1 → (False ∨ (p3 → ((p4 ∧ p5) → p2))))) ∨ True) ∧ p1) → p2) → p3) ∨ p3) → p5) ∧ p3) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_396953646917817712071710804261 : ((((False ∨ (((p4 ∧ p1) ∨ (p3 ∧ ((p4 → ((((True → p5) → p2) → p2) ∧ True)) ∧ p3))) → (((p5 → p4) ∧ p5) ∨ True))) ∨ p2) ∧ True) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41677285477875020502755493929 : (((((True ∧ p2) ∧ (False ∧ (True ∨ p4))) ∨ (((True ∧ p4) → p1) → ((p2 ∧ (p3 ∧ p4)) ∧ (p5 ∨ (p2 → (p4 ∨ True)))))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199445957312889171919883422213 : (((p2 ∧ (p4 ∧ ((True ∨ p3) → False))) ∨ p2) → (((p3 ∧ ((p2 → ((p5 ∧ True) ∧ (p5 → p4))) ∨ p1)) ∧ ((True → p3) ∨ True)) ∨ p2)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653294123829882206395553811926 : ((((p2 → ((((p5 ∧ (p3 ∧ p5)) → p4) ∨ p5) ∧ ((((p1 ∨ (True → ((p4 → p4) ∨ True))) ∧ p5) → False) ∧ p2))) ∧ (False ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88697857856184287772643474486 : (((((p2 ∧ p2) ∨ True) ∨ p3) → ((False ∨ ((p5 → p1) ∨ (p1 ∨ (p5 → (p1 ∨ True))))) ∧ ((p1 ∧ (True → p5)) ∧ (p5 ∨ p1)))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∧ p2) ∨ True) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165815129260809242299316662491 : (((p1 ∧ (p5 ∧ False)) ∧ ((p2 ∧ (p4 ∨ (p5 ∧ True))) ∨ (((p4 ∨ p4) ∧ p4) ∧ p1))) ∨ ((p5 ∨ p2) → (((p5 ∧ True) ∧ p3) → p3))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256698109012657051249864627321 : ((p1 ∨ p1) → (((((p3 → ((((p5 → ((False → False) ∧ False)) ∨ p5) ∧ False) ∧ ((p2 ∧ p4) → p3))) → p4) ∨ (p4 → p1)) ∨ p5) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602166954562371527448867063708 : ((((p5 ∧ ((p1 ∧ p2) ∨ (False ∨ ((((p2 ∨ p1) → p2) ∧ (p1 → True)) ∨ (p1 → (((p4 → (False ∧ p1)) → p1) ∧ p2)))))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259877902146362122543357639009 : ((p1 → p4) → ((p5 → (((((p4 → p3) → False) ∧ (p4 ∨ (p4 ∨ p5))) ∧ p4) ∨ p5)) ∧ ((p5 → p3) ∨ ((True ∨ (p5 ∨ p4)) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52699530838345367658627968588 : (((p2 → (False ∧ (((p1 → (p4 ∧ (False → p1))) → False) ∧ (False ∨ p5)))) ∨ (((False ∧ p1) ∧ p5) ∨ ((p3 ∧ p4) → (p2 ∨ True)))) ∨ p5) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58874308357306864509437636175 : (((False ∧ False) ∨ (((p3 ∧ (p2 ∨ (False ∨ (p2 → p3)))) ∧ (True → ((False → p2) ∧ p2))) ∨ ((p3 → (p1 → p3)) ∨ (True ∧ False)))) ∨ False) := by
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
theorem thm_5_vars_201078050096189460434917982557 : ((p5 ∨ ((p4 ∧ False) → ((p5 ∨ p4) ∧ p1))) → ((p2 ∨ (p1 ∨ ((((True → ((p1 ∨ False) → p4)) ∨ p4) → (p5 ∨ p5)) ∧ p1))) ∨ True)) := by
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
theorem thm_5_vars_117505273991819832537805831956 : ((p2 ∧ (((p5 ∧ p2) → (True → (p3 ∨ ((p5 ∧ p1) ∧ ((p5 ∧ (p2 ∧ (False ∧ ((p1 ∨ p3) ∧ p3)))) ∧ p4))))) ∧ p4)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629369633519923928039307807999 : ((((((p1 ∧ (((p3 ∧ (False ∨ True)) ∨ p1) → ((p4 ∨ False) ∧ ((False → ((p4 ∨ True) ∧ (p4 ∨ p3))) → p5)))) → p4) ∨ True) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165083320862652306709694391439 : (((False ∨ (p4 ∧ (False → ((p3 ∧ (p4 ∧ p3)) → (p1 ∨ (p1 ∨ (False → True))))))) → False) ∨ ((True ∧ p3) → (True ∧ (p2 ∨ (True ∧ True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46897278470948881077135066159 : (((((p5 ∧ (((p2 ∧ p2) → (((p1 ∧ ((((p4 ∨ p2) → p2) ∨ True) → p4)) ∧ p5) ∨ p5)) → False)) → p1) ∨ p3) ∨ (False ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158289348508925216465230422382 : ((((p5 → p4) ∧ p5) → ((((((p4 ∧ p2) ∧ (p1 ∨ False)) → (p5 ∧ p3)) ∧ False) ∨ p2) ∧ False)) ∨ ((p5 ∧ p2) → ((p5 ∧ p2) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748397592739842417345535809233 : ((((p2 → p3) → ((True → (p5 ∧ (p2 ∧ (p5 → ((p5 ∨ (True ∨ True)) → p4))))) ∨ ((True ∧ p2) → (((p1 ∧ p1) ∧ True) → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59284118012404502277322213837 : (((p3 ∨ p3) ∨ ((p4 ∨ (((p5 ∧ (p4 ∨ (p5 ∨ p4))) ∨ ((((p4 → p1) → p3) ∨ p2) → True)) ∧ (True ∨ p1))) ∨ (p2 → p2))) ∨ p3) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651162433615604679396963542445 : (((((((p5 ∧ True) → p2) ∧ p2) → (((p4 ∨ p2) → (p4 ∧ True)) ∨ ((p5 → (p1 ∧ (True → (True ∧ p5)))) → True))) ∧ (True ∨ p2)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68733106915554529902038376449 : ((p4 → (((((True ∧ True) ∧ p5) ∧ ((p2 ∨ ((True ∧ False) ∧ p3)) ∨ p2)) ∨ (p3 ∧ (True ∨ p2))) ∨ (True ∧ (p1 ∧ (p4 ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110855348011716468637041345529 : (((((True ∧ ((((p2 → ((True → ((p3 ∨ (p5 ∨ p4)) ∧ p2)) → p3)) ∧ (p5 ∨ p4)) → p4) ∨ p1)) ∧ p2) → p1) ∧ True) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261351623340351013243958719666 : ((p5 → False) → (True ∧ ((p4 ∨ (p5 ∨ p1)) → ((((True → p1) ∧ ((p2 → ((p1 ∧ p5) ∧ p4)) ∨ p5)) ∧ p3) ∨ (p4 → (p4 → p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h8 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h9 := h1 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141032460045549950256857965489 : ((((p3 → p2) ∨ (((True ∧ p2) ∧ p1) → p4)) ∧ (p3 ∨ (True ∧ ((((p4 → False) ∧ p5) ∨ (False ∨ False)) → p1)))) → (p2 ∨ (p1 → p1))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260040672838763493569946786112 : ((p2 → False) → (((((p3 → (p5 → p4)) ∨ p3) ∨ p2) → (p1 → ((((p2 ∨ (True ∨ (p1 → p1))) → False) ∨ (p3 → p3)) ∨ p2))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
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
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205289823190102229844122653783 : (((p2 ∧ (p2 ∨ p2)) ∨ (False ∨ p1)) ∨ (p4 → (((p4 → False) → ((((True ∧ False) → p2) ∧ ((p2 ∨ p4) ∨ p2)) ∧ (p4 ∧ p5))) ∨ False))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218121671992229684225058916077 : (((p2 → p2) ∧ (p5 → p3)) → ((p4 ∨ True) ∧ (((True ∧ p1) ∨ p3) → (p1 → (((True ∨ False) → False) ∨ (((True → p2) ∨ p3) ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h1.left
    let h13 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52836716039196141079204847023 : ((((p2 → (p2 → True)) → (((p2 ∨ (False ∨ p5)) ∨ p3) ∧ (False ∧ p1))) → ((((p5 ∧ p3) ∧ (p5 ∨ False)) ∨ (p4 ∧ p4)) ∨ p3)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → (p2 → True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736754852518601616726040463372 : ((((p2 → p1) ∧ ((p4 → p3) ∨ ((p2 ∧ (p2 ∧ (True ∧ ((((True ∧ p2) ∨ (p3 ∧ p1)) ∨ p4) ∧ p3)))) ∧ (p5 ∨ (p2 ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312961086362970593564977474969 : (p3 ∨ ((((p2 → ((((False ∨ p4) ∧ (((p1 ∨ (p4 ∨ p5)) ∧ True) → (False → False))) → ((p3 ∧ p2) ∨ p5)) ∨ False)) → p5) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192566172171826811750613640093 : (((p2 ∨ (p4 → ((p2 ∨ (p5 → p5)) ∨ p4))) ∨ True) → ((True → (((False ∨ p2) ∧ False) ∧ True)) → (((True ∨ (p1 → True)) ∧ p1) ∨ p2))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- We need to get the left conjuct of h7 based on <expert-advice>.
      let h8 := h7.left
      -- We need to get the right conjuct of h8 based on <expert-advice>.
      let h9 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51910352180766627406829848359 : (((((True ∨ (p1 → ((((False ∧ p3) ∧ False) ∨ p3) → False))) → p3) ∨ (False → p5)) ∨ ((p1 ∨ (((p5 → p5) ∧ p5) → p2)) ∨ p5)) ∨ p5) := by
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
theorem thm_5_vars_64483356508996429823778413909 : ((p1 ∨ (((p4 ∨ p2) → ((p3 ∧ ((((p5 ∧ ((p1 → p1) ∧ p3)) → p1) → True) ∧ True)) → False)) ∨ ((p2 ∨ p4) ∧ (p1 → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612806960864294469575584882698 : ((((((p2 ∨ p1) ∨ (((p4 ∨ p4) → ((p2 ∧ p2) ∨ (((p4 ∨ p2) → p5) ∨ p3))) ∧ ((False ∨ p4) ∨ False))) ∨ (p2 ∨ False)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309925088865736169092106533236 : (p2 ∨ ((((((p3 ∧ True) ∨ (p5 → False)) ∨ p3) → False) ∧ (p5 → (False ∧ (p3 ∧ (p3 ∧ False))))) ∨ ((p3 ∧ ((True ∧ p4) → p1)) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705023814465131641626952052093 : ((((p2 → ((((True ∨ False) ∨ (p5 ∨ p5)) ∧ p5) ∨ p1)) → ((p5 ∨ (((False → (((True ∨ p4) ∧ p2) ∨ p3)) ∨ p2) → p5)) → p5)) ∨ p2) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : ((False → (((True ∨ p4) ∧ p2) ∨ p3)) ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h5
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674502961718324859897278448 : ((((p5 → ((p5 → (p1 ∧ (False ∨ p3))) ∨ (((True ∧ p4) ∨ False) ∧ p5))) → p3) ∨ ((p1 → (p2 ∨ (p4 ∨ True))) → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



