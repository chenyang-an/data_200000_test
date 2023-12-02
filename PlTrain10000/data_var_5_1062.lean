variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735741331540425957298835040989 : ((((p5 ∨ p3) ∧ (p1 → (True ∧ (p3 → (((p3 → ((True ∨ (False ∨ p4)) ∧ (p5 ∧ ((False ∨ (p4 ∨ p2)) ∧ p5)))) ∧ True) → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615002433430702166433489693774 : (((((((p5 ∧ True) ∧ False) ∨ ((((p5 → True) ∨ False) ∧ (p4 → False)) → ((p5 → p3) → p5))) → (p2 ∨ ((p1 → p3) → False))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147839559009115117004831047952 : (((p3 ∨ ((False ∨ (p3 ∧ (False → ((True ∨ (p1 → p3)) ∧ p1)))) → ((p2 ∨ (p4 → p4)) ∨ p1))) → p4) ∨ (p1 ∨ ((p3 ∨ p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52673644766707744053566304947 : (((p1 ∨ ((p1 ∨ ((True ∧ (p3 ∨ ((p5 ∨ False) ∨ p2))) ∨ p1)) ∧ p1)) ∨ (((p3 → (p1 ∧ p4)) ∧ p3) → (p1 ∧ (p1 ∧ p3)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h9
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- One of the premise coincides with the conclusion.
  exact h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328314281195093821090413820261 : (True → ((p3 → (p3 ∧ (False ∧ ((p2 ∨ (p2 → (((p5 ∧ (p4 → p1)) ∨ (p3 ∨ p1)) ∧ p3))) → False)))) ∨ (((p2 ∧ p5) → True) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60837386584384385148410910238 : ((True ∧ (False ∨ (p2 → (p5 ∨ (((p2 ∧ (((p1 → False) ∧ (p3 → p1)) ∧ (p2 ∧ p3))) ∨ False) ∨ (((p4 → p4) ∧ p2) ∨ True)))))) ∨ p5) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62620404307202419908625354911 : ((p4 ∧ ((((((p5 → False) → p5) ∧ (True → ((p4 ∨ True) → ((p1 ∧ False) → (p5 ∨ p3))))) → p1) ∨ ((p3 ∨ p1) ∧ p4)) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246740906936870454740453525669 : ((p5 ∧ p5) ∨ (((p3 ∨ (p1 ∨ (True → (p3 ∧ p1)))) → ((((((((True ∧ p5) → p2) ∧ p3) ∧ p2) ∨ p4) → p4) ∨ p3) ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55576431814516345465173568050 : (((False ∨ (True → (p2 ∧ (p3 ∧ p2)))) → (((p5 ∨ p5) ∧ (False ∨ p5)) ∧ ((True → (False ∨ ((p5 ∧ (False → False)) ∧ p1))) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173456814643991055659068226052 : ((((((p2 ∧ p4) ∧ ((((False → p3) → p4) → True) ∨ p1)) ∧ p5) ∨ p3) ∧ p5) → ((((p2 ∨ (p2 ∧ p5)) → p1) ∧ (p5 → True)) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655973200302347327432343773574 : ((((((((p5 ∨ (p3 ∧ (p2 → (p4 ∨ (p5 → p1))))) → p1) → (p5 ∨ p2)) ∨ True) ∨ ((False → (p3 ∨ False)) ∧ p3)) ∨ (p2 ∧ p5)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_303156074556285825110764242244 : (False ∨ (p3 → (p4 → ((((p3 → p2) ∧ (p5 ∧ (((p2 ∧ (p2 ∨ True)) ∧ p2) ∧ (p3 → (((p4 ∧ p1) ∨ p1) ∨ p3))))) ∨ p5) ∨ p4)))) := by
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
theorem thm_5_vars_61556605299584995426865017413 : ((p1 ∧ ((((p5 ∧ p2) ∨ p3) → ((p1 ∨ p4) ∧ False)) ∨ ((p1 ∨ ((p3 → False) ∨ (True → p1))) ∧ (True ∧ ((p1 → p5) ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329534511477529940105506024178 : (True → ((p4 ∧ True) ∨ ((p1 → p4) ∨ ((p4 ∨ True) → (p5 ∨ (((p1 → p4) → p5) ∨ ((p4 ∨ ((True ∨ True) ∧ True)) ∨ (p1 → p2)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
theorem thm_5_vars_135608019449516014286657375011 : (((True ∧ (((p1 ∧ (p1 ∧ (True ∨ False))) → True) → (p5 ∧ ((p5 → p5) ∧ False)))) ∨ (p4 → ((p1 ∧ False) → p2))) ∨ (p1 ∨ (p4 → p1))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263398976581006108964142689550 : (True ∧ ((((True ∧ p1) ∧ (p3 ∧ (p4 ∨ (p1 ∧ (p4 ∧ p3))))) ∧ ((((False → p4) → p4) ∨ (p5 ∧ p1)) ∨ p3)) ∨ ((p3 → p3) ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40753887399590404110111557944 : (((((p5 ∨ False) ∧ (((p5 → p2) ∧ (((p2 ∨ (p2 ∧ p1)) ∨ False) → ((p5 ∧ (False ∨ True)) ∧ False))) ∨ (p3 → False))) → p1) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137983686941542409983460143594 : ((p5 ∨ ((p4 ∨ p2) ∧ (((p3 ∧ p2) ∨ (((p5 → False) → ((p2 ∨ p1) ∧ (p4 ∨ p1))) ∧ (p1 ∨ p3))) ∧ False))) ∨ (p2 → (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150051425406723372500262508994 : ((True → (((((p4 ∨ p4) ∧ (((p4 ∨ p2) → p4) ∧ ((False ∧ p1) → False))) → False) ∨ (p2 ∧ p1)) ∨ True)) ∨ (((p2 → p3) → p3) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48453533966406497206501985433 : (((((((p1 → (((((False → p3) → False) → p4) ∧ False) ∧ (True ∨ p1))) → (p3 ∨ p4)) ∨ p3) ∧ False) ∧ True) ∧ ((p2 ∨ True) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199266776554268000365740227044 : ((((((p4 → p2) ∨ p5) ∨ p1) ∧ p2) ∨ True) → (((True ∧ p5) → (((p1 → p3) ∧ ((p2 ∨ (p3 → p3)) → p4)) ∧ (True ∨ p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38046028335178487961935963379 : ((((((False ∨ p4) ∧ (True ∨ ((p2 → p5) → ((False ∧ (p2 ∨ (p4 ∨ (True ∧ (p1 → p5))))) ∧ p3)))) → True) → (p1 ∧ p2)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345591884302674331697258734431 : (p3 → (((p4 ∨ True) ∧ ((((p5 → p4) ∧ p1) → (True ∨ p1)) → (((((p1 ∧ (p5 ∧ p4)) ∨ p5) ∧ p1) ∧ (False ∧ p5)) ∧ False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174288647694478755228100484642 : (((True → ((p1 ∧ False) ∧ (p3 ∧ ((p2 ∧ True) → p1)))) ∧ (p5 → (p2 → p1))) → (p5 ∨ ((p5 ∨ False) ∨ ((p5 ∨ p3) ∨ (p1 → p5))))) := by
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
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328454827146154081989167688564 : (True → ((((p4 ∧ p3) → (False → ((False ∨ p1) ∧ p5))) ∧ (p3 ∨ (p5 ∧ (p5 ∨ (p4 ∧ False))))) → (((p2 → True) → False) → (p1 → False)))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : (p2 → True) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h8
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h15 : (p2 → True) := by
        -- Implications on the right can always be decomposed.
        intro h16
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h17 := h3 h15
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- False on the left can always be used.
      apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233811995032167908949723309442 : ((p3 ∨ (p3 → p1)) → ((((((p5 ∧ False) → p4) ∧ True) ∧ p4) ∧ (((((p1 ∨ False) → p2) ∨ ((True ∨ p1) ∨ p1)) → p4) → False)) → p3)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h11 : ((((p1 ∨ False) → p2) ∨ ((True ∨ p1) ∨ p1)) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- One of the premise coincides with the conclusion.
            exact h6
          case inr h17 =>
            -- One of the premise coincides with the conclusion.
            exact h6
        case inr h18 =>
          -- One of the premise coincides with the conclusion.
          exact h6
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h19 := h4 h11
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318560943265787381419580352181 : (p4 ∨ (((p1 ∧ (p3 ∧ (((True ∧ (p4 ∨ (p4 ∨ (((p3 ∨ p3) → (p1 ∧ True)) ∧ True)))) ∧ (p1 ∧ p3)) ∨ p5))) ∨ p2) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56274465965999595172637881984 : (((p4 → ((True ∨ p4) → p3)) ∨ ((((False → True) → p4) → (p4 ∨ p2)) → ((((False ∨ p5) ∨ (True → (p4 → True))) → p1) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658169448427976974382689670308 : ((((p4 ∧ (True ∧ ((((p2 ∨ (p4 ∧ p3)) → (p3 ∧ (p2 → (p5 → ((p2 ∨ p2) → p1))))) ∨ p5) ∨ (p1 → False)))) ∨ (True ∨ p2)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_42664351539752107208393549100 : (((p4 ∨ (((False → (p4 ∨ (True → p3))) ∨ p5) ∧ (p3 ∧ (p1 → (p3 ∨ (True ∧ (p2 ∨ (p5 ∧ (p3 → (p5 ∧ p4)))))))))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42007290470793768326039795185 : ((((p3 → p2) ∧ (((p3 ∨ (p4 ∧ (p4 → p1))) ∨ (p5 ∧ ((False ∨ False) ∧ ((False → p3) ∨ p4)))) ∨ ((True ∨ p3) → True))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242124536775706102734533827608 : ((p2 → True) ∧ ((((p4 ∨ p1) ∧ (p5 → ((((p3 ∧ False) ∧ p2) → ((p1 ∨ p3) ∧ p2)) ∨ (p4 ∧ p3)))) → (True ∧ (p2 ∨ False))) ∨ True)) := by
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
theorem thm_5_vars_67572340943760536765594576357 : ((p1 → ((p2 ∨ p4) ∨ ((p1 ∧ ((p1 → ((p1 → (p5 → (((False ∧ p5) → (True → p2)) → True))) ∨ p3)) → p5)) ∨ (True ∨ p1)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_66499369826539360517622593976 : ((True → ((True ∧ ((((p3 → False) ∨ ((p4 ∧ False) ∨ p3)) ∧ (True → (True ∧ (p5 ∧ ((p1 ∨ p1) ∧ p1))))) ∨ (True → True))) ∨ p3)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263883109972816005839849255784 : (True ∧ ((((p3 ∧ ((p2 ∨ ((p2 → p3) → (p3 ∨ p5))) → p4)) → p2) ∨ p1) ∨ (((p4 ∨ True) → (p3 ∨ (p3 ∧ True))) → (p2 → True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160852271277650233552306231636 : ((((p4 ∨ (True ∨ p4)) → p5) ∧ (p1 ∨ (p5 ∧ (((p4 ∨ False) ∨ p3) → (p4 ∨ (True ∨ p1)))))) → (((p4 ∧ (p5 ∧ False)) ∧ p1) ∨ p5)) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p4 ∨ (True ∨ p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351010074637953461131554983958 : (p4 → ((True → ((((True ∧ (p2 → ((p5 ∨ False) ∨ p3))) → p2) → (p3 ∧ ((p1 ∨ p4) → ((False ∧ p4) ∧ p4)))) ∧ p1)) ∨ (p4 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134107127970446779167893445748 : (((((p3 ∨ ((p5 ∨ p1) → (p3 ∨ ((p1 ∧ ((p5 ∧ (p4 ∨ p4)) → True)) ∧ p4)))) → p4) ∧ (p5 ∧ p1)) ∨ True) ∨ (p3 ∧ (p1 ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113395113230570787327254329915 : (((p2 → (((True ∧ p2) ∧ (True ∧ (p4 ∨ ((((p1 → p3) → (p4 ∨ False)) → p1) → (p2 ∧ p5))))) ∨ p2)) ∧ (p3 ∨ p1)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159095457730409826410286708544 : ((True → ((((p2 → p1) → (p3 ∧ p3)) → (p5 → True)) → ((((p4 ∨ p1) ∨ True) ∨ False) ∨ p2))) ∨ (True ∨ (((False ∨ p1) → True) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150168941040939681408881603262 : ((p1 → ((True ∨ p2) ∧ (p2 ∨ (False ∧ ((p5 ∧ (p5 ∧ ((p5 ∨ False) ∨ (p5 ∨ (False ∨ p3))))) → p3))))) ∨ (p2 ∨ (p5 → (p2 → p5)))) := by
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
theorem thm_5_vars_46757143748423555837994144156 : (((p2 → ((((p4 ∨ (p4 ∧ (((p3 ∨ True) ∧ True) ∧ p1))) → (p4 → (p1 ∧ p4))) ∨ ((False ∧ p1) ∧ p4)) ∨ p3)) ∧ (p3 → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_35932236586166093245511125932 : ((p3 → (((p3 → p4) ∨ ((((p3 → False) ∨ (p5 ∧ True)) ∧ ((((True ∧ p1) → p5) ∧ p1) ∧ False)) ∨ p5)) ∨ (True ∨ (p3 → p1)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_588703740298762262520454534090 : (((((p2 ∧ (p1 → (False ∧ ((p2 → ((p1 ∨ False) ∨ False)) ∧ ((((p3 → ((p4 → p5) ∨ p1)) ∧ p1) ∨ p5) ∧ p4))))) ∨ p2) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347610861061354474559225211883 : (p3 → (((p5 ∧ p1) ∨ (p3 ∧ p2)) ∨ ((p5 ∨ p1) ∨ ((p4 ∧ ((p4 ∧ False) ∧ (p1 → (((p4 ∨ (p5 ∧ True)) ∧ True) ∨ p3)))) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41505831895380736796812727800 : ((((False ∨ (True → (False ∨ ((False ∧ p4) → (True ∨ (True ∨ False)))))) → (p2 → (p1 ∨ ((p1 ∧ ((p1 ∧ True) ∨ False)) → p4)))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747387013420772709572128506567 : ((((p5 ∨ p5) → (p5 ∧ (((p5 → (((p4 → (p1 ∧ p5)) ∨ p5) → p2)) → (False ∧ ((p2 ∧ p4) ∨ p5))) → ((p1 ∧ p4) ∨ True)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Implications on the right can always be decomposed.
  intro h4
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181957245795933568938611824604 : (((((p3 → (((p4 → False) → p4) → False)) ∨ True) ∨ p5) ∨ p3) ∧ (((p4 ∨ ((p2 ∨ (p4 → ((False → p1) ∨ True))) ∧ p3)) ∨ True) ∨ False)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_397453478356657712200545560037 : ((((p2 ∨ (((p2 ∨ p3) ∧ (((True ∧ (((True ∧ p5) ∨ p5) ∧ ((p5 → (p4 → p5)) → p1))) → p4) → (p3 → p2))) → p1)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_315402438569329943000080294403 : (p3 ∨ (((p1 ∨ p3) ∨ p2) ∨ ((p1 ∨ ((p5 → ((p3 ∧ ((True ∨ (((p5 ∨ p4) ∨ (True ∨ p4)) ∨ p1)) ∨ p5)) ∨ p4)) → True)) ∨ p5))) := by
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
theorem thm_5_vars_777349208303118682159170344543 : (((p1 ∨ ((p3 ∧ ((((p3 ∧ ((p4 ∨ p2) → ((False ∧ False) ∨ p3))) ∨ p3) ∨ p2) → (p2 ∧ p5))) ∨ (p3 → ((True ∧ p5) ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171003809589019493118835923617 : ((p3 ∨ ((p4 ∧ (p2 → (p5 → (((p2 → p5) → p4) → p3)))) → (p4 → p4))) ∧ ((False → False) ∧ ((p1 ∨ p2) ∨ (p2 ∨ (p5 ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  exact h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807944266541728286935284529580 : (((p4 → ((p1 ∧ p3) → ((((((p5 ∧ False) ∨ False) ∨ ((p3 ∧ p1) → p5)) ∧ p1) ∧ ((p4 ∨ ((True ∧ False) ∨ p1)) ∧ False)) ∨ p4))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599731916104419168534908566374 : (((((p3 → p4) ∨ ((((p5 ∧ p3) ∧ ((p4 → ((False → p4) ∧ True)) → p3)) → p1) → (p1 ∨ (p1 → (p2 ∨ (False ∧ p3)))))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754598058229599649148483457491 : (((False ∧ (p2 ∧ (p5 ∧ (((((((p5 ∧ False) ∧ p2) ∨ (p3 ∧ p2)) → p1) ∧ (p4 ∨ p2)) ∨ (True ∧ (False ∨ True))) ∨ (p2 ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257683416084836034793236731284 : ((p3 ∨ p3) → ((p2 → ((p1 → (False ∧ True)) ∨ (p5 ∧ (p3 ∧ ((p5 ∧ (p5 ∨ ((p5 ∨ False) ∨ True))) ∧ (p1 → False)))))) ∨ (False → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354028746417547880129164094304 : (p4 → (p4 → ((((((False → p5) ∧ p5) ∨ (p5 ∧ (p2 → False))) → p3) ∨ ((p1 → p5) ∨ (p2 ∨ (True ∨ (p1 ∧ p1))))) ∧ (p3 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675659360323674862009128668603 : ((((((p4 ∨ (((p2 → (p4 ∧ (p3 ∧ True))) → (True ∨ p4)) → True)) → (p2 ∧ False)) → (p1 ∨ p2)) ∧ (True → (p4 → (p2 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260851578045125990818714808953 : ((p4 → True) → ((((p3 ∧ p2) ∨ p5) ∧ ((((p4 ∧ p5) → p4) ∨ p5) → p2)) → ((((p1 → (p2 ∨ (p1 ∧ p4))) → p4) ∧ p3) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h11 : (p1 → (p2 ∨ (p1 ∧ p4))) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h13 := h4 h11
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h15 : (((p4 ∧ p5) → p4) ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h16 := h7 h15
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h17 : (p1 → (p2 ∨ (p1 ∧ p4))) := by
      -- Implications on the right can always be decomposed.
      intro h18
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h19 := h4 h17
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322562054825032137434315048045 : (p5 ∨ ((p2 ∨ ((p4 ∨ (p5 ∨ ((p1 ∨ ((p5 ∨ p4) ∨ False)) ∧ (((False ∧ p3) → p4) ∨ p1)))) → ((p5 → (p5 → False)) → False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147724032611072940931506257645 : ((((((p5 → False) → (p5 ∧ p5)) ∨ p2) ∧ (((p1 ∧ (False → (p5 → p3))) ∧ (p5 → p3)) → False)) → p3) ∨ (p4 ∨ ((False → False) ∨ p5))) := by
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
theorem thm_5_vars_165818719666054805830590768825 : (((p5 ∧ (False ∧ False)) ∧ (((p1 ∨ (p4 ∧ p4)) ∧ (p4 ∨ (p3 ∨ p2))) ∨ (p3 ∧ p2))) ∨ (p4 → (p2 → (((True ∨ p2) → False) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46213794489225629349057308495 : ((((((((p3 → p3) ∧ p3) ∧ (p4 ∨ ((True ∧ p4) ∨ p2))) → p2) ∧ ((p2 ∨ (p5 ∧ p4)) → True)) ∧ (p4 → p1)) ∧ (p2 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173858807417564537738851438670 : (((((p2 → ((p1 ∨ True) ∧ ((p4 → (True ∧ True)) ∨ True))) ∨ p2) ∧ True) → False) → (((True → ((p3 → p5) ∨ False)) ∧ False) ∧ (p4 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p2 → ((p1 ∨ True) ∧ ((p4 → (True ∧ True)) ∨ True))) ∨ p2) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
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
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (((p2 → ((p1 ∨ True) ∧ ((p4 → (True ∧ True)) ∨ True))) ∨ p2) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
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
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h6
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : (((p2 → ((p1 ∨ True) ∧ ((p4 → (True ∧ True)) ∨ True))) ∨ p2) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
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
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h9
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151393897615310628310677134804 : (((((((p4 ∧ True) ∨ p2) → (False ∧ False)) ∧ (p4 → True)) ∧ (p5 ∧ (p3 ∨ (p2 → p1)))) ∧ (True → p4)) → (((True ∧ True) → p3) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h8.left
  let h12 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h15 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h16 := h6 h15
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h17 : ((p4 ∧ True) ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h16
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h18 := h9 h17
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- False on the left can always be used.
    apply False.elim h19
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h20.left
  let h23 := h20.right
  -- Conjunctions on the left can always be decomposed.
  let h24 := h22.left
  let h25 := h22.right
  -- Conjunctions on the left can always be decomposed.
  let h26 := h23.left
  let h27 := h23.right
  -- Disjunctions on the left can always be decomposed.
  cases h27
  case inl h28 =>
    -- One of the premise coincides with the conclusion.
    exact h26
  case inr h29 =>
    -- One of the premise coincides with the conclusion.
    exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177904500773672369165286680875 : ((((p1 ∨ ((False → ((False ∨ True) ∧ p5)) → False)) ∨ (p4 ∨ p1)) ∨ False) ∨ (((((p5 ∧ p4) → p1) ∧ False) → ((p2 → p4) → p5)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233203031422371818706304740963 : ((p5 ∧ (False → True)) → ((True ∧ (((((True → p5) ∧ True) → p4) ∧ True) ∧ ((((((True → p1) ∨ p1) → p4) ∨ p2) → p4) → False))) ∨ p5)) := by
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
theorem thm_5_vars_114800707908880222540184455295 : (((((p3 → p2) ∧ (p2 → (p3 → p4))) ∧ (((p2 ∧ p2) ∧ p5) → False)) ∧ (((p3 ∧ (False → True)) → p2) → (p4 → p5))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740450066086813632903047831780 : ((((p1 ∨ p4) ∨ ((p1 ∧ ((False → p5) → p2)) ∧ (p4 ∨ (((((False ∧ (p3 ∧ p1)) ∧ p5) ∨ ((p3 ∨ False) ∨ p3)) ∨ p1) ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164458763675052172246366492122 : ((((False ∨ ((p2 → (True ∧ ((p5 ∧ (p1 → p4)) ∨ (p4 ∧ p5)))) ∨ p2)) ∧ p2) ∧ p2) ∨ ((p2 ∨ True) ∨ (True ∧ (p1 ∧ (p5 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134916251255988988313643190420 : (((((((((p4 ∨ True) → (p4 → True)) ∧ False) ∧ (p5 → p4)) → p2) → ((p4 ∨ True) → p3)) ∨ True) ∧ (False ∧ False)) ∨ (p5 → (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58248015481715755881853279234 : (((p5 ∧ p1) ∧ ((p3 ∧ ((((((p5 → p5) ∧ p4) ∨ p4) ∨ (p1 → (p3 ∨ (p5 ∧ (p3 ∧ (p1 ∨ False)))))) → False) ∧ True)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65227479990541701943690830649 : ((p3 ∨ ((p5 ∧ (p3 ∨ (((((p2 ∨ ((p1 ∧ p1) ∨ (p3 ∨ p2))) ∨ (((p3 ∨ p4) ∨ p1) ∨ p4)) ∧ False) ∧ p1) ∧ p3))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42249357797342915251917887583 : (((False ∧ (p5 → (((p2 ∨ True) ∧ p4) → ((False ∨ (p4 ∧ (p3 ∨ True))) ∧ ((True ∧ (p5 ∨ (p4 → p4))) ∧ (True → p1)))))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162029148636957185023312195040 : ((p4 → (((False → p5) ∧ (p1 → ((p5 ∨ p5) → p3))) ∨ ((True → (p1 → (p5 ∧ True))) → p3))) → ((True → False) → (p2 ∧ (p1 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54244739754359145298303013101 : (((((p4 ∨ p3) → (p4 → p2)) ∧ (p1 ∧ p4)) ∧ (p3 → (((p3 → (p5 ∧ (p4 → ((p5 ∨ p2) → p2)))) ∨ True) ∧ (p4 ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138519487845654492771728150637 : ((((((p5 → ((p4 ∧ p4) → (p5 ∧ p3))) ∨ ((p1 → (p5 ∨ (p5 ∨ False))) ∧ (p4 → p4))) ∨ p2) ∨ p5) ∧ p5) → ((False ∧ False) ∨ p5)) := by
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
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755577428227555572866115953841 : (((p1 ∧ (((((p2 ∧ (((p1 → p1) ∧ p3) ∨ False)) ∧ (((((p2 ∨ p5) ∨ p4) ∧ False) ∨ p4) → (p5 → False))) ∧ p1) ∨ p5) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182791828985729170091375135036 : (((p4 ∧ ((True ∨ p4) → p5)) → ((p1 ∨ (p1 ∨ p2)) → True)) ∧ (p2 ∨ ((p4 ∨ p2) ∨ ((((p3 ∧ p5) ∧ (p2 ∧ p5)) ∧ False) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
theorem thm_5_vars_249715631421146095552484898306 : ((p5 ∨ p5) ∨ ((((p1 ∨ (p1 ∨ (p5 ∨ (((((p3 ∨ False) ∧ (False ∨ p1)) ∨ p1) ∧ False) ∧ False)))) → p2) ∨ (p3 ∧ (p4 ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54379702311845603388482205055 : (((p2 → (p4 ∨ ((True ∧ True) → (p2 → p3)))) ∧ (((p3 ∨ p3) ∨ (True → (((p4 → p4) ∨ (p1 ∨ p2)) → (False ∨ p2)))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136955196339556645804414233944 : (((True ∧ p4) → (p3 ∧ (p3 ∨ ((((p1 → False) → (p5 ∧ p4)) ∨ (p1 → p5)) ∨ (((p5 ∨ p5) → p3) ∨ p5))))) ∨ (p3 → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249486082419574330990068464936 : ((p5 ∨ p1) ∨ (((True ∨ p1) → ((True ∨ (p1 ∧ (True → p4))) ∧ ((p2 ∧ (((True → (p3 → True)) → False) ∧ p2)) ∧ True))) → (p4 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : (True → (p3 → True)) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h12 := h8 h9
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16790995870941223839229175581 : (((((p3 → (((False ∧ p3) ∧ False) ∧ p5)) ∨ False) ∨ (p1 ∧ ((((True → p3) → (True ∨ p2)) ∧ p2) → p3))) ∨ ((False ∧ p4) → p5)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48962823679222673270059506396 : (((((p5 ∧ (False ∨ ((p4 ∧ p2) → ((((p3 ∧ p3) ∨ True) ∨ (p2 ∨ (p4 → p4))) ∨ True)))) ∧ p5) ∨ p4) ∨ ((False ∧ p5) → p2)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_927491649977274931486591221988 : (((((False ∧ ((p3 ∨ ((p2 → p5) ∧ True)) ∧ p4)) ∨ p5) ∧ (p2 ∧ (p2 ∧ ((p4 ∨ p1) → (p4 → ((p3 → True) ∨ (p2 → False))))))) → p5) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190396628847459431098637922616 : (((p2 ∧ (((False ∨ p2) ∧ p5) ∨ (False ∧ p5))) ∨ False) ∨ ((p2 ∧ ((((p3 ∨ p2) ∨ False) → (p1 ∨ ((False ∨ False) ∨ p3))) → p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321611983506499089207733669905 : (p4 ∨ (p3 → (((p3 ∧ (((p2 ∨ p1) → (p2 → True)) → p1)) ∨ ((((False ∧ True) → (p1 → p4)) ∨ True) ∨ p2)) ∨ ((p4 ∨ p3) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_53067389271456443665188216404 : (((p1 ∧ (((p2 → p1) ∨ (p4 ∧ ((p3 → p3) ∨ p2))) ∧ True)) ∧ ((p4 ∧ p3) ∨ (((True → ((p5 ∧ True) → True)) ∨ p5) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336935483557383013936280888643 : (p1 → (((p4 ∧ (True ∧ (((((True ∨ p4) → False) ∨ ((p1 ∨ ((p2 → p1) → True)) ∧ (p3 ∧ False))) ∧ p4) ∨ p4))) ∨ True) ∧ (True ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85983783091814242535445033523 : ((((p2 → (p3 ∨ (p2 → (False → p1)))) → (False ∧ p5)) ∧ ((((False ∧ p4) ∨ (p2 → p2)) ∧ (p5 ∨ (p4 → (p2 ∧ p2)))) ∨ True)) → p5) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h13 : (p2 → (p3 ∨ (p2 → (False → p1)))) := by
          -- Implications on the right can always be decomposed.
          intro h14
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h15
          -- Implications on the right can always be decomposed.
          intro h16
          -- False on the left can always be used.
          apply False.elim h16
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h17 := h2 h13
        -- We need to get the right conjuct of h17 based on <expert-advice>.
        let h18 := h17.right
        -- One of the premise coincides with the conclusion.
        exact h18
  case inr h19 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h20 : (p2 → (p3 ∨ (p2 → (False → p1)))) := by
      -- Implications on the right can always be decomposed.
      intro h21
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- Implications on the right can always be decomposed.
      intro h23
      -- False on the left can always be used.
      apply False.elim h23
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h24 := h2 h20
    -- We need to get the right conjuct of h24 based on <expert-advice>.
    let h25 := h24.right
    -- One of the premise coincides with the conclusion.
    exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215519222627576903434883387379 : ((p4 ∧ (p2 ∧ (False ∧ p4))) ∨ (((((((p3 ∨ p2) ∨ (p5 ∨ ((p1 ∨ p5) → False))) → (p1 ∧ p4)) ∧ p3) → False) ∨ (p1 ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44314327795142954503347914059 : ((((((p4 ∧ (p4 ∧ p2)) → (((True → p2) ∨ (p1 ∧ p3)) ∨ p5)) → (p3 ∧ p1)) ∨ (p4 ∧ ((p4 ∨ True) ∨ (True → True)))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348995044426452417275567041162 : (p3 → (p4 ∨ ((p3 → ((p3 → ((False → False) ∨ False)) ∨ False)) ∧ (((((False ∧ p3) ∧ p4) ∧ ((True ∨ (p3 ∨ p1)) ∧ p4)) ∨ p5) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780979574943437286799930201710 : (((p2 ∨ ((p1 ∧ (p5 ∨ True)) → ((((p3 ∧ p2) ∨ ((False → (True → (False → p4))) ∨ ((p5 ∨ p5) ∧ p3))) → (p2 ∧ p2)) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192893168108029555379932756812 : (((p3 ∨ ((p1 → p4) → (False ∨ True))) ∧ (p4 ∨ False)) → ((((p5 ∨ ((True ∧ False) → p2)) → (((p2 ∨ True) → p3) ∨ p4)) ∨ p1) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h19 =>
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h22 =>
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h23 =>
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724777116692147628061797859882 : ((((p3 ∨ (p2 → p2)) ∧ ((p3 ∨ (p3 ∧ (((p5 ∨ False) ∨ False) ∧ True))) → (p4 → ((p5 ∨ (p1 ∨ (p4 ∨ (False ∧ False)))) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731796443784564665537683341199 : ((((p3 → (p2 → False)) → ((((False → ((p5 ∧ True) ∨ p4)) ∧ p5) → (((((False ∨ False) → p2) → (p4 ∨ p2)) → p3) ∨ True)) ∨ p1)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197137696042775615919714471248 : (((True → (((p3 ∨ p2) ∧ p3) ∨ p4)) ∨ p1) ∨ ((((p5 ∧ False) ∨ p3) → p3) ∨ (((((p4 → True) ∨ p2) ∨ p2) ∧ p5) ∨ (p1 → True)))) := by
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
theorem thm_5_vars_134387340730011300667307528733 : (((p5 ∨ ((((((p3 ∧ p1) ∨ (p4 ∧ (p5 → (p4 ∧ True)))) ∧ False) → p5) ∨ ((p5 ∨ p3) ∨ p1)) → p1)) ∨ p2) ∨ (False → (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



