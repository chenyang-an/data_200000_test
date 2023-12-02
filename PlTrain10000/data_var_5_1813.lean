variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49599255265238989786157042480 : ((((((p3 → (False ∧ False)) ∨ (False ∧ p1)) ∧ (True ∨ p4)) ∧ (((p5 → p2) ∨ (p1 ∧ p2)) → (True ∨ p1))) → (p2 ∨ (p5 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299142108669947924036579374599 : (False ∨ (((((p5 ∧ True) ∧ (p1 ∧ (False ∧ False))) ∨ (p3 ∧ (((p5 ∨ False) ∨ (False → ((p3 ∨ False) → (p4 → True)))) ∧ p5))) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165707093184030841920101618423 : ((((p4 ∧ (p1 → True)) ∨ False) ∧ (p3 ∧ (False ∨ (p3 ∨ ((p3 ∨ (p3 ∨ p4)) ∨ p4))))) ∨ (((False → p4) ∧ True) ∨ (True ∧ (p3 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174801592324879199498516216357 : (((True → p3) ∧ (((p4 ∧ (((True → p5) → p2) ∨ p4)) ∧ p1) ∨ (p1 ∨ p4))) → ((p3 → (p2 ∨ (p1 → p5))) ∨ (p3 ∨ (False ∧ p5)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h10
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h14 := h2 h13
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h18 := h2 h17
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h20 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h21 := h2 h20
      -- One of the premise coincides with the conclusion.
      exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44856631937039593909142050741 : ((((p5 ∧ (p5 ∨ p3)) ∨ ((p1 → (p4 ∧ (False ∨ (((True → True) ∧ ((False ∧ p5) ∧ (True ∨ (p5 → p3)))) ∧ p5)))) ∨ False)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42096458685783404932331447061 : ((((True ∧ p4) → (((((p1 ∨ p5) → ((p1 ∧ ((p1 ∧ p4) ∨ p2)) ∧ (p4 ∨ (p1 ∨ p3)))) → p2) → p1) ∧ (p3 ∧ p2))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111210653333212625534727242529 : ((((p4 ∨ (p5 ∨ p3)) ∨ (p3 ∨ ((((p4 ∧ True) ∨ (((p4 → p3) ∧ p5) → ((False ∧ p4) ∧ p3))) → p5) ∧ p3))) ∧ p5) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322298030838249715694199450661 : (p5 ∨ ((((p5 ∨ (p5 ∧ (p5 ∨ False))) ∨ ((p2 → ((p5 ∨ ((False ∧ p5) ∨ (p1 ∨ p2))) ∧ ((p5 ∧ p2) ∧ p5))) ∨ True)) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234427847980497485195717723156 : ((p2 → (False ∧ p4)) → (p4 ∨ ((True ∧ ((((p2 ∨ p4) ∧ p4) ∨ False) ∧ p2)) → ((((p4 → p1) → (True ∧ p4)) → p4) ∨ (p2 ∨ p2))))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713752141254878601403278240371 : (((((p3 → ((p1 → p5) → p1)) ∧ p1) → (((p4 ∨ p1) ∨ ((False ∨ (True ∨ p2)) → (p1 → p1))) ∧ (p3 ∧ (p5 ∨ (p5 ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595529618466886862096892572228 : (((((p2 ∨ ((((True ∨ ((p5 ∨ p3) ∨ p2)) ∧ p3) ∨ False) ∨ p2)) ∨ ((((True → p4) → p5) ∨ p1) ∨ (p5 → (p5 ∧ False)))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357471764729488625116864113972 : (p5 → ((p4 → p2) → ((((p2 → p4) ∨ (((False ∨ False) → p5) ∧ (p1 → (p5 ∧ (p3 ∨ (True ∨ p3)))))) → False) ∨ (False → (p5 → p2))))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654313719719955374345021924665 : ((((((p1 ∨ (((p1 ∨ False) ∨ (False ∧ True)) ∨ (p3 ∨ (((True ∨ p2) ∨ p1) ∨ True)))) ∨ ((False ∨ p4) ∧ p1)) ∨ p1) ∨ (p3 ∧ p3)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193814651658072855365627206369 : ((p5 ∧ (((True ∧ p1) ∧ (p1 ∧ p4)) ∧ (p3 ∨ True))) → (((False → (True ∧ (p4 ∧ (p2 ∨ ((p5 ∧ p2) ∨ p2))))) → (True ∧ p3)) ∨ p1)) := by
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
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h7.left
  let h11 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198042861486199298038321440976 : (((p2 ∧ p1) ∨ (True ∧ ((p4 → p2) ∧ p4))) ∨ (((p1 ∨ (False → (((((p5 ∧ False) → p1) ∨ p5) ∧ p1) ∧ (False ∨ p3)))) ∨ p3) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344963032311234625369471501878 : (p3 → (((p1 → (p2 ∨ (p1 → ((False ∨ ((p3 ∧ (p5 ∨ p3)) → p4)) → ((((p3 → p4) → p5) ∧ p5) ∨ (p3 → p4)))))) ∨ p4) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : (p3 ∧ (p5 ∨ p3)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337802746505883640701935653434 : (p1 → (((p1 ∧ (p4 ∨ (p3 → True))) ∧ (((True → (p1 → (p2 ∧ False))) → p5) → False)) → ((p4 ∧ ((p3 ∨ (p5 ∨ p3)) ∧ True)) ∨ p2))) := by
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
  cases h6
  case inl h7 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h8 : ((True → (p1 → (p2 ∧ False))) → p5) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h11 := h9 h10
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h13 := h11 h12
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- False on the left can always be used.
      apply False.elim h14
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h15 := h4 h8
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h17 : ((True → (p1 → (p2 ∧ False))) → p5) := by
      -- Implications on the right can always be decomposed.
      intro h18
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h19 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h20 := h18 h19
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h21 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h22 := h20 h21
      -- We need to get the right conjuct of h22 based on <expert-advice>.
      let h23 := h22.right
      -- False on the left can always be used.
      apply False.elim h23
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h24 := h4 h17
    -- False on the left can always be used.
    apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694019200818984726276413902828 : ((((((p4 ∨ p2) ∨ (True ∧ ((p2 ∨ (False → p1)) ∨ p4))) → (p5 ∨ p3)) ∨ ((p4 ∧ False) ∨ (((p2 → True) ∨ (p1 ∨ False)) ∨ p1))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678021871790706687323177894257 : (((((False → (((p4 ∧ (p1 → p3)) ∨ ((p5 ∨ p4) ∨ (p3 ∨ p4))) ∧ p5)) ∧ (True ∧ (False ∧ False))) ∨ (((True ∨ False) → p2) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711560300751485390645339589837 : ((((p1 → ((True ∨ (p5 → True)) ∧ p2)) ∧ (((p3 ∨ p3) ∨ (p5 ∨ ((False ∧ (False ∧ True)) ∨ ((p5 → p5) ∧ p4)))) ∨ (p4 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55114418132312339491584606757 : (((((p3 ∨ (True ∧ p2)) ∨ p2) ∧ p4) ∨ ((((p5 ∨ p1) ∨ p5) ∨ p5) → (p3 ∨ (((False ∨ True) → (False ∧ (False → False))) → p2)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h5
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h6 : (False ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h7 := h5 h6
        -- We need to get the left conjuct of h7 based on <expert-advice>.
        let h8 := h7.left
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h11 : (False ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h12 := h10 h11
        -- We need to get the left conjuct of h12 based on <expert-advice>.
        let h13 := h12.left
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h16 : (False ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h17 := h15 h16
      -- We need to get the left conjuct of h17 based on <expert-advice>.
      let h18 := h17.left
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h20
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h21 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h22 := h20 h21
    -- We need to get the left conjuct of h22 based on <expert-advice>.
    let h23 := h22.left
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255902072862241330393349145660 : ((True ∨ p1) → (p5 → ((p2 ∨ False) → (((p1 ∧ (p5 ∧ (p3 ∧ p4))) ∨ ((p1 ∧ (p3 → (p4 → False))) ∨ p2)) ∨ ((p5 ∧ True) → p1))))) := by
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
    cases h1
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680188006394426350406533905083 : (((((((True → False) ∨ p5) ∨ (p3 ∨ ((p3 → ((p3 ∧ p5) → True)) → (True → p3)))) ∨ (p5 → p4)) → (p1 ∧ ((False ∧ p3) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189764440784820693303656376089 : ((p5 ∨ ((p3 ∨ True) ∧ (False ∨ (False ∨ (p1 ∨ True))))) ∧ (False → (False ∧ (p2 ∨ ((p4 ∨ (p2 ∧ (True ∧ ((False ∧ p1) ∨ p2)))) ∨ p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180676699578615882869173946249 : (((((True ∨ p3) ∨ p3) ∨ (p1 → p2)) → ((False → (p4 → p1)) ∧ p4)) → ((p1 → ((p4 → (((p3 ∧ p3) ∨ p1) → p3)) ∧ True)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True ∨ p3) ∨ p3) ∨ (p1 → p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
theorem thm_5_vars_147817880419357899913599251561 : (((p5 ∧ ((p4 → (True ∧ p1)) ∧ (((False ∨ ((False ∨ p4) ∨ (p3 ∧ p2))) ∨ (p4 → p4)) → False))) → p4) ∨ (p2 → (p5 ∧ (p1 ∧ p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((False ∨ ((False ∨ p4) ∨ (p3 ∧ p2))) ∨ (p4 → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165508207047929416762605252970 : (((((False ∨ (p2 → ((p1 ∧ p5) ∧ p5))) ∧ True) ∨ True) → (p4 ∧ (p4 ∧ (p4 ∨ p4)))) ∨ (((p2 ∨ (p1 ∨ False)) ∨ (p3 ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113047225863404958033425651827 : (((p1 ∨ ((((((p4 ∨ False) → p1) ∨ (p4 ∧ False)) ∧ (False → False)) ∨ (p5 ∨ ((False ∨ p3) → p3))) → (p2 ∧ p1))) → False) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337939127458287528625477587970 : (p1 → ((((p1 ∧ p2) ∨ (((p1 → False) ∧ p1) → (False ∨ p3))) ∧ p5) ∨ ((True → False) ∨ ((((p5 → p1) ∨ p3) ∨ p2) ∧ (p2 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149941969504429635802835577235 : ((p3 ∨ (p4 ∧ ((p3 ∨ ((((p4 → p2) ∨ False) → (p4 ∧ (p3 → p1))) ∨ ((True ∨ p1) ∧ p2))) ∧ True))) ∨ ((p2 → p3) → (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178870000332257345836544443176 : (((True ∧ p1) ∧ ((p5 ∧ (((True → True) ∧ False) ∨ p4)) ∧ (p5 ∨ p5))) ∨ (True ∧ (((p1 ∨ True) ∨ (False ∨ p5)) ∨ ((p4 ∧ p5) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_116409367163055560669956542353 : (((False ∨ (p4 ∧ p5)) → (False ∨ ((p5 → (p1 ∨ p2)) ∨ ((p4 → (((p2 → p1) ∨ ((p4 ∨ p3) → p1)) ∨ p5)) ∧ p5)))) ∨ (p4 → p5)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197438464918779189867631638683 : ((((False ∨ (p1 ∧ False)) ∧ True) ∧ (False ∧ p2)) ∨ ((((p3 → (True ∧ (p3 ∧ False))) ∧ False) ∧ (p1 → p1)) → (p4 ∨ (p3 → (False ∨ p4))))) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587116800288261171060187696858 : (((((p2 → ((((((p1 ∧ ((False ∧ p4) ∨ True)) ∨ p4) → True) → p5) → (((False → p3) → (p1 ∨ p4)) → True)) → p5)) ∧ p3) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190960622757329681513263873062 : (((p5 ∨ ((p4 ∨ p1) ∨ p1)) ∧ (p1 ∨ (p2 ∨ p1))) ∨ (p5 ∨ ((((True ∧ p4) → p5) ∨ (p5 ∧ ((p2 ∨ (p4 ∧ p4)) → p3))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60249450369817986518640047957 : (((False → False) → (((((((p1 ∨ (False → ((False ∨ p3) ∧ ((False ∧ (True ∧ p2)) ∧ p2)))) ∧ p5) ∨ True) ∧ p4) → p1) ∧ p5) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136902000443263331624598712455 : (((p5 ∨ p1) ∨ (((((p5 → (True ∧ True)) ∧ (True ∨ p4)) ∧ ((False ∧ ((p2 ∨ False) ∨ p1)) ∨ p1)) ∧ p1) ∧ p1)) ∨ ((p4 ∧ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2306311573144505302039183000 : (((((p1 ∨ (((p5 → p3) → p4) ∧ p2)) ∧ p1) → (True ∧ True)) → False) → ((((False → p1) ∧ (p3 ∧ (p1 → p2))) → p5) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ (((p5 → p3) → p4) ∧ p2)) ∧ p1) → (True ∧ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213372251318747266283304879252 : (((p5 ∧ (p5 ∨ p1)) ∧ p5) ∨ (((False → ((p3 ∨ True) ∧ (False ∧ (((p3 ∧ p2) → True) ∧ (p4 ∨ ((p4 → p4) ∧ p1)))))) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196790964919124403934366090329 : ((((p3 ∧ p3) ∨ (p4 ∧ (p2 ∧ p2))) ∧ p5) ∨ (p1 → ((p5 → ((p4 ∧ ((p2 → ((p5 → (False → p5)) ∧ p5)) → p5)) ∨ p5)) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172210314757030797250583747965 : (((((p2 ∧ p5) ∧ False) → (p3 ∨ ((p2 → p5) ∨ True))) → (p4 ∧ (p2 ∨ p5))) ∨ ((p3 ∨ (p2 ∧ ((p1 → (p3 ∧ p5)) → p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66673256760541428924287027214 : ((True → ((p3 → ((p5 ∧ (p3 ∧ True)) → p5)) → ((p1 ∧ (((p1 → p3) ∧ (True ∧ p3)) ∨ p3)) ∨ (((p3 → False) ∨ p4) → True)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_266080060074676166020988960628 : (True ∧ (p2 → (((p1 → (((p4 ∨ False) → ((p4 ∨ True) ∨ (p5 → p4))) ∧ True)) → p1) ∨ (p2 ∧ (p5 → ((p2 ∧ (p5 ∨ p3)) → p2)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208360940590956348479982901058 : (((False ∧ False) ∨ (p2 ∨ (p4 ∨ p5))) → (((((p4 ∧ p4) → ((p5 ∧ p5) ∧ p5)) ∧ p2) ∨ p4) ∨ ((((False ∧ p5) → p2) ∨ p3) ∨ p1))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h13
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- False on the left can always be used.
        apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299143595032031259259507859598 : (False ∨ (((((p3 ∨ (p5 → False)) ∨ True) → (p3 ∨ (((p1 ∨ True) ∨ False) ∨ ((p4 → (True → p4)) ∧ (False → (True → p3)))))) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44997369903180045505342145741 : ((((False ∧ p1) ∨ ((True → p2) ∨ (((False ∨ (False → (p2 ∨ (False ∨ (p3 → False))))) → (p4 ∧ (True ∧ (p5 ∨ p3)))) ∨ p3))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689618087737324115710480281561 : ((((((p2 ∧ ((True ∧ True) ∨ p4)) ∨ False) → (False ∧ ((p5 ∨ p5) ∨ (p1 → p1)))) ∨ ((p3 ∧ p4) ∧ ((False → False) → (p2 → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158443219926589220307310828401 : (((p3 ∨ p1) ∨ (((((p4 ∧ False) ∨ p5) ∧ p3) → p5) ∧ ((False ∨ ((p4 ∨ p3) ∧ False)) ∨ p4))) ∨ (True → ((p2 ∨ True) ∨ (False ∨ p2)))) := by
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
theorem thm_5_vars_210377450374739031064153780966 : (((True ∨ (p4 → True)) ∨ p4) ∧ (p1 ∨ (((p1 → p3) → ((((p2 ∧ p5) → ((p2 ∧ p3) ∧ p1)) ∨ True) ∨ False)) ∨ ((True → p2) → False)))) := by
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
theorem thm_5_vars_148726261382678601896974535561 : (((True → (False → (((p3 ∧ p2) ∨ p3) → p1))) → (True → ((((p2 ∨ p1) ∧ (p5 ∧ p1)) → p1) → False))) ∨ (((p4 ∨ p4) ∧ True) → p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341982570231521105811823382996 : (p2 → ((((True ∨ p5) ∨ ((p3 → p2) ∨ (True → (((p3 → p1) → (p4 → (True ∧ False))) ∧ False)))) → (p3 ∨ p4)) ∨ ((p2 → False) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44520380783991469147213232103 : (((((p5 ∨ p5) → ((p4 ∧ False) ∧ (p3 ∧ (p5 → p2)))) ∨ ((((p5 ∨ True) ∧ p3) ∧ p3) ∨ ((p4 ∧ p1) → (p3 → True)))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125043794234051825892959205241 : ((((False → p4) → p3) ∧ (((False → p3) ∧ (p5 ∧ (((p5 ∨ p3) ∨ p2) ∧ (False ∨ ((p4 → p3) → p1))))) ∨ (True ∧ False))) → (p1 ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h13 =>
          -- False on the left can always be used.
          apply False.elim h13
        case inr h14 =>
          -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
          have h15 : (p4 → p3) := by
            -- Implications on the right can always be decomposed.
            intro h16
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h17 : (False → p4) := by
              -- Implications on the right can always be decomposed.
              intro h18
              -- False on the left can always be used.
              apply False.elim h18
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h19 := h2 h17
            -- One of the premise coincides with the conclusion.
            exact h19
          -- We have shown the premise of h14, we can now drive its conclusion.
          let h20 := h14 h15
          -- One of the premise coincides with the conclusion.
          exact h20
      case inr h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h22 =>
          -- False on the left can always be used.
          apply False.elim h22
        case inr h23 =>
          -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
          have h24 : (p4 → p3) := by
            -- Implications on the right can always be decomposed.
            intro h25
            -- One of the premise coincides with the conclusion.
            exact h21
          -- We have shown the premise of h23, we can now drive its conclusion.
          let h26 := h23 h24
          -- One of the premise coincides with the conclusion.
          exact h26
    case inr h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h28 =>
        -- False on the left can always be used.
        apply False.elim h28
      case inr h29 =>
        -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
        have h30 : (p4 → p3) := by
          -- Implications on the right can always be decomposed.
          intro h31
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h32 : (False → p4) := by
            -- Implications on the right can always be decomposed.
            intro h33
            -- False on the left can always be used.
            apply False.elim h33
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h34 := h2 h32
          -- One of the premise coincides with the conclusion.
          exact h34
        -- We have shown the premise of h29, we can now drive its conclusion.
        let h35 := h29 h30
        -- One of the premise coincides with the conclusion.
        exact h35
  case inr h36 =>
    -- Conjunctions on the left can always be decomposed.
    let h37 := h36.left
    let h38 := h36.right
    -- False on the left can always be used.
    apply False.elim h38
  -- Conjunctions on the left can always be decomposed.
  let h39 := h1.left
  let h40 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h40
  case inl h41 =>
    -- Conjunctions on the left can always be decomposed.
    let h42 := h41.left
    let h43 := h41.right
    -- Conjunctions on the left can always be decomposed.
    let h44 := h43.left
    let h45 := h43.right
    -- Conjunctions on the left can always be decomposed.
    let h46 := h45.left
    let h47 := h45.right
    -- Disjunctions on the left can always be decomposed.
    cases h46
    case inl h48 =>
      -- Disjunctions on the left can always be decomposed.
      cases h48
      case inl h49 =>
        -- Disjunctions on the left can always be decomposed.
        cases h47
        case inl h50 =>
          -- False on the left can always be used.
          apply False.elim h50
        case inr h51 =>
          -- We want to use the implication h39 based on <expert-advice>. So we show its premise.
          have h52 : (False → p4) := by
            -- Implications on the right can always be decomposed.
            intro h53
            -- False on the left can always be used.
            apply False.elim h53
          -- We have shown the premise of h39, we can now drive its conclusion.
          let h54 := h39 h52
          -- One of the premise coincides with the conclusion.
          exact h54
      case inr h55 =>
        -- Disjunctions on the left can always be decomposed.
        cases h47
        case inl h56 =>
          -- False on the left can always be used.
          apply False.elim h56
        case inr h57 =>
          -- One of the premise coincides with the conclusion.
          exact h55
    case inr h58 =>
      -- Disjunctions on the left can always be decomposed.
      cases h47
      case inl h59 =>
        -- False on the left can always be used.
        apply False.elim h59
      case inr h60 =>
        -- We want to use the implication h39 based on <expert-advice>. So we show its premise.
        have h61 : (False → p4) := by
          -- Implications on the right can always be decomposed.
          intro h62
          -- False on the left can always be used.
          apply False.elim h62
        -- We have shown the premise of h39, we can now drive its conclusion.
        let h63 := h39 h61
        -- One of the premise coincides with the conclusion.
        exact h63
  case inr h64 =>
    -- Conjunctions on the left can always be decomposed.
    let h65 := h64.left
    let h66 := h64.right
    -- False on the left can always be used.
    apply False.elim h66



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319883843792483307835250764962 : (p4 ∨ ((p5 ∧ (False ∨ (p4 → p1))) ∨ (p2 → (p5 ∨ ((p3 → (p3 ∨ p4)) → ((p2 ∨ p1) ∧ (p3 → (p4 ∨ ((True ∨ p3) ∨ p5))))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263815491245604494490102278258 : (True ∧ ((p3 → ((((p5 → p1) → ((False ∨ p1) ∧ (p4 ∧ (p2 → True)))) ∨ True) ∨ False)) ∨ ((p5 ∨ p5) → ((p1 ∧ p4) ∨ (p4 ∧ p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_329327140326334045778189643275 : (True → (((p2 ∨ p2) ∧ p2) → (((p3 ∨ ((p4 ∧ p4) ∨ p3)) ∧ (p5 ∧ p5)) ∨ (False → ((((p1 ∧ False) → p2) ∨ (p1 → False)) → p1))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151318025466960669310200836209 : (((p4 ∨ (p4 → ((p2 → (False → (p4 → False))) → (((p1 → p5) → (p2 → False)) ∧ (p1 ∧ p4))))) → p3) → ((False ∧ (p2 ∧ p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165071193602267456150634568548 : (((p3 ∧ (p4 → ((((p4 ∧ False) ∨ p2) ∧ (True ∧ (True → (True ∧ p2)))) ∨ p3))) → p4) ∨ ((True ∧ False) → (p2 → (p5 ∧ (p5 ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327972760550504201726133860010 : (True → ((((p2 → (p3 → True)) → False) ∧ ((p1 ∨ (p1 ∧ (((False → p5) ∨ True) ∧ (p5 ∨ ((True ∨ p2) ∧ p2))))) → p1)) → (p5 ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p2 → (p3 → True)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h5
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h11 : (p2 → (p3 → True)) := by
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h14 := h9 h11
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43940871415143307552479926016 : ((((((p1 ∧ p2) → (((False ∧ p5) ∧ False) ∨ True)) ∨ (((False → True) → ((False ∨ p2) → (p3 ∧ False))) ∨ True)) ∨ (p2 → p1)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615361891475853663417874987396 : ((((((True ∨ (p1 ∧ (p2 ∧ p3))) ∧ ((((True ∨ False) ∧ p3) ∧ (False ∧ p5)) ∨ False)) ∨ (((False ∨ p5) ∨ p5) ∨ (p4 → p4))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_230227178569667703796359952248 : (((True ∨ p2) ∧ p4) → ((True → (p3 ∨ p3)) → ((p5 ∨ ((p4 ∧ p5) ∨ (p2 ∨ (p4 ∨ True)))) → ((p1 → ((True → p2) ∨ p4)) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h1.left
      let h15 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h1.left
        let h21 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h21
      case inr h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h1.left
          let h27 := h1.right
          -- Disjunctions on the left can always be decomposed.
          cases h26
          case inl h28 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h27
          case inr h29 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h27
        case inr h30 =>
          -- Conjunctions on the left can always be decomposed.
          let h31 := h1.left
          let h32 := h1.right
          -- Disjunctions on the left can always be decomposed.
          cases h31
          case inl h33 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h32
          case inr h34 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h32
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h35 =>
    -- Conjunctions on the left can always be decomposed.
    let h36 := h1.left
    let h37 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h36
    case inl h38 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h39 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h40 := h2 h39
      -- Disjunctions on the left can always be decomposed.
      cases h40
      case inl h41 =>
        -- One of the premise coincides with the conclusion.
        exact h41
      case inr h42 =>
        -- One of the premise coincides with the conclusion.
        exact h42
    case inr h43 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h44 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h45 := h2 h44
      -- Disjunctions on the left can always be decomposed.
      cases h45
      case inl h46 =>
        -- One of the premise coincides with the conclusion.
        exact h46
      case inr h47 =>
        -- One of the premise coincides with the conclusion.
        exact h47
  case inr h48 =>
    -- Disjunctions on the left can always be decomposed.
    cases h48
    case inl h49 =>
      -- Conjunctions on the left can always be decomposed.
      let h50 := h49.left
      let h51 := h49.right
      -- Conjunctions on the left can always be decomposed.
      let h52 := h1.left
      let h53 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h52
      case inl h54 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h55 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h56 := h2 h55
        -- Disjunctions on the left can always be decomposed.
        cases h56
        case inl h57 =>
          -- One of the premise coincides with the conclusion.
          exact h57
        case inr h58 =>
          -- One of the premise coincides with the conclusion.
          exact h58
      case inr h59 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h60 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h61 := h2 h60
        -- Disjunctions on the left can always be decomposed.
        cases h61
        case inl h62 =>
          -- One of the premise coincides with the conclusion.
          exact h62
        case inr h63 =>
          -- One of the premise coincides with the conclusion.
          exact h63
    case inr h64 =>
      -- Disjunctions on the left can always be decomposed.
      cases h64
      case inl h65 =>
        -- Conjunctions on the left can always be decomposed.
        let h66 := h1.left
        let h67 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h66
        case inl h68 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h69 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h70 := h2 h69
          -- Disjunctions on the left can always be decomposed.
          cases h70
          case inl h71 =>
            -- One of the premise coincides with the conclusion.
            exact h71
          case inr h72 =>
            -- One of the premise coincides with the conclusion.
            exact h72
        case inr h73 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h74 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h75 := h2 h74
          -- Disjunctions on the left can always be decomposed.
          cases h75
          case inl h76 =>
            -- One of the premise coincides with the conclusion.
            exact h76
          case inr h77 =>
            -- One of the premise coincides with the conclusion.
            exact h77
      case inr h78 =>
        -- Disjunctions on the left can always be decomposed.
        cases h78
        case inl h79 =>
          -- Conjunctions on the left can always be decomposed.
          let h80 := h1.left
          let h81 := h1.right
          -- Disjunctions on the left can always be decomposed.
          cases h80
          case inl h82 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h83 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h84 := h2 h83
            -- Disjunctions on the left can always be decomposed.
            cases h84
            case inl h85 =>
              -- One of the premise coincides with the conclusion.
              exact h85
            case inr h86 =>
              -- One of the premise coincides with the conclusion.
              exact h86
          case inr h87 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h88 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h89 := h2 h88
            -- Disjunctions on the left can always be decomposed.
            cases h89
            case inl h90 =>
              -- One of the premise coincides with the conclusion.
              exact h90
            case inr h91 =>
              -- One of the premise coincides with the conclusion.
              exact h91
        case inr h92 =>
          -- Conjunctions on the left can always be decomposed.
          let h93 := h1.left
          let h94 := h1.right
          -- Disjunctions on the left can always be decomposed.
          cases h93
          case inl h95 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h96 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h97 := h2 h96
            -- Disjunctions on the left can always be decomposed.
            cases h97
            case inl h98 =>
              -- One of the premise coincides with the conclusion.
              exact h98
            case inr h99 =>
              -- One of the premise coincides with the conclusion.
              exact h99
          case inr h100 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h101 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h102 := h2 h101
            -- Disjunctions on the left can always be decomposed.
            cases h102
            case inl h103 =>
              -- One of the premise coincides with the conclusion.
              exact h103
            case inr h104 =>
              -- One of the premise coincides with the conclusion.
              exact h104



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719203610363530178205183663911 : ((((p2 ∧ (p3 ∨ (p3 ∨ p3))) ∨ ((p1 ∨ ((p4 ∨ p2) ∨ p2)) ∧ ((p5 → ((p4 ∨ ((True ∨ p5) ∨ True)) → (True ∨ p4))) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308712193249260340422608205025 : (p2 ∨ ((p5 ∨ (p2 ∨ (p1 ∨ (((p3 ∨ p2) ∨ (False ∨ ((p2 ∨ (p2 ∨ False)) → (((False → False) → p3) → (p4 ∨ p4))))) → False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596660312273285465607283139853 : (((((((p5 ∨ p2) ∧ (p4 ∨ p2)) → p5) ∧ ((p1 → (p2 → p1)) → ((p3 ∧ p3) → (((True ∨ p5) → False) ∨ (True ∧ True))))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53027518207629633565674435743 : ((((p2 → (p2 ∧ (False ∧ p2))) → (p3 ∧ ((p4 ∨ p1) ∧ False))) ∧ ((p5 → ((True ∧ p1) ∨ False)) ∧ (p3 ∨ (p1 ∨ (p1 → True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_379691704811755810437556974374 : (((((((p3 ∨ ((False → True) ∧ True)) → (((False → p1) → ((p2 ∨ ((True → p4) ∨ True)) ∧ (p3 ∧ p3))) ∧ True)) ∧ p3) ∧ False) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_107815883092878754408712435779 : (((p4 ∧ p3) ∨ (p1 ∨ (((((p1 ∨ p1) ∧ (p2 → True)) ∨ ((p3 → ((p4 ∨ False) → (p2 ∧ p5))) ∨ True)) ∨ p1) ∨ p1))) ∧ (p1 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48028515861130309929153106951 : ((((p4 ∧ (p3 → ((True → p5) → (p1 ∧ ((p1 ∨ p3) ∨ True))))) → (p4 ∨ (False ∧ (p1 ∨ (p1 → (p4 → p1)))))) → (p1 → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723372254083078027141048867343 : (((((False ∧ p5) → True) ∧ ((False ∨ p2) → ((True ∨ p2) → (p1 ∧ ((p1 → ((p3 → ((True → (p3 ∨ p1)) → p4)) ∧ p4)) ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148002297006221794214138713877 : ((((p4 → (((p4 ∧ p1) → (p5 → (False ∨ p1))) → (p1 ∨ (p2 ∧ (p3 ∨ p5))))) → p5) ∨ (p2 ∧ False)) ∨ (p5 ∨ ((True ∨ p5) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_752221344946823591523926365480 : (((True ∧ (p4 → ((((p3 ∨ (p1 ∨ p1)) → (((True → (p5 ∨ (p5 ∧ False))) ∧ False) ∧ ((p4 → p1) ∧ (p1 → p1)))) → p5) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228544528253976273107012931599 : ((p1 ∨ (p4 ∧ p2)) ∨ (p3 → (p5 → (((((False ∧ (p2 ∧ p1)) ∨ p2) ∨ True) → True) ∧ (((p4 ∨ False) ∨ (p3 ∨ True)) ∨ (True ∨ p2)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224977217277043225885930441710 : (((True ∧ False) ∧ False) ∨ ((p5 ∧ (((False ∧ ((p5 → ((p3 → (True ∧ (True → False))) → (p3 ∨ p2))) → p5)) ∧ (p1 ∧ p3)) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613108539370732865802450151575 : (((((((((((False ∨ False) ∨ p5) ∨ True) ∧ p5) → p4) ∨ (p2 ∨ ((False ∨ p1) ∧ (True → (p5 ∨ True))))) → p2) → (p4 ∧ p2)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_180983859050636614159957224372 : (((False ∧ p1) ∨ (((False → p5) ∨ p5) → ((p3 ∨ p4) ∨ (p1 → p2)))) → ((((p1 → False) ∨ True) ∨ (p2 → (p3 → (p5 ∨ p2)))) ∨ False)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157776953711854842021437396623 : ((((p2 ∨ (((p5 ∨ p3) ∨ ((False ∨ False) → p2)) → p5)) ∨ p4) ∨ (False ∨ (True ∨ (p3 ∧ p5)))) ∨ ((p3 ∨ p5) ∨ ((p1 ∨ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340691642490267081721857603254 : (p2 → ((((p1 ∨ (((((False → p2) ∧ (p4 ∧ p1)) ∧ (p2 → p3)) ∧ p5) ∧ (True ∧ (False ∨ (p2 → (p4 ∧ False)))))) ∧ p5) ∧ False) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61552400202347791081723069671 : ((p1 ∧ (((p1 ∨ (p4 → ((p4 → p4) ∧ p5))) ∨ True) ∧ ((p2 ∨ (((p3 ∧ (p3 → p5)) ∧ ((p4 ∨ p5) ∨ True)) ∨ p3)) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115807176002212777562718537629 : (((((p4 → p1) → p1) → p3) ∧ (p5 ∨ (((p4 → False) ∧ True) → ((True ∧ (p2 ∧ False)) ∧ (p3 ∧ ((False ∨ p5) ∨ False)))))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118516238660961025200226563319 : ((p3 ∨ (((p5 ∧ True) ∧ p2) → ((((p4 ∨ p4) ∧ (p2 ∨ p1)) → (((p4 → p1) → p3) → p1)) ∨ ((True ∨ p2) → True)))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643803509134874735209638028100 : ((((p5 ∧ ((True → ((p3 ∨ p1) ∧ p5)) ∨ ((p3 ∧ (p4 → (p4 → (True ∧ (p2 ∨ p3))))) ∨ (False → ((p5 ∧ p5) ∨ p4))))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777983647498265888117962487600 : (((p1 ∨ (((p4 ∨ p2) ∧ p5) → (p1 ∨ (((p3 → (p5 ∧ ((p2 ∧ (False ∨ (p4 ∨ p4))) → ((p1 ∧ p2) ∨ p3)))) ∧ p2) ∨ True)))) ∨ p3) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253806423393157749394831351097 : ((p1 ∧ p2) → ((((((p4 ∨ (p3 ∧ p4)) ∧ p4) ∨ p5) ∧ p3) ∨ (False ∧ True)) ∨ ((p1 → (p4 → (((p3 ∨ p3) → p4) ∧ p1))) → p2))) := by
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669126954889279906033275232650 : ((((((((p2 → p3) ∨ ((False ∧ (p2 ∨ p5)) → False)) ∧ p4) ∨ (((p3 ∧ False) → p4) ∧ (p3 ∨ p4))) → p3) ∨ ((True ∧ p3) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227807627869642273838806218247 : ((p2 ∧ (True ∧ p2)) ∨ ((p3 ∧ (p5 ∧ p4)) → (((((((p3 → True) ∧ False) ∧ p2) → (p2 → False)) → False) ∧ p5) ∨ ((False ∧ p5) → p1)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251661314852634065911531946100 : ((p3 → p2) ∨ ((p4 ∧ ((p2 → ((((p1 → p3) → (False ∨ False)) ∨ p3) ∨ p3)) → ((False → True) → (p4 → (p3 ∧ (p3 → p1)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192443207368387422060607721647 : ((((p2 ∧ (((True → False) ∧ p3) ∨ p5)) → p1) ∨ True) → ((((p1 → p2) ∧ p5) ∨ True) → (((p2 → p4) ∨ (p2 → (p4 → p4))) ∨ p2))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Implications on the right can always be decomposed.
      intro h15
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702373993499332924531255111513 : ((((((True ∨ (p4 → (p5 ∨ (p1 ∨ False)))) → p1) ∨ p1) ∨ (((p3 ∧ p5) → ((p5 ∨ (p2 ∨ True)) → (p4 ∧ p4))) ∨ (p5 → p5))) ∨ p3) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171674432550415971654728976839 : (((False ∨ ((p5 ∧ (p5 ∨ (p5 ∧ ((False → False) → p1)))) ∨ (True ∨ True))) ∨ p4) ∨ ((p5 → ((False → (True → p4)) ∨ (True ∧ p5))) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_240044187449705130054142882760 : ((p4 ∨ True) ∧ (p3 ∨ ((((False → (p3 ∨ p4)) → ((False → (p5 ∧ (p5 ∨ True))) ∧ p4)) ∨ True) ∨ (((p1 ∨ p4) ∨ (p3 → p3)) ∧ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653032548856155894340095818217 : ((((True → (((p5 ∧ (((p5 ∨ (False ∧ (p5 ∨ p5))) ∨ p3) ∨ p4)) ∧ (p2 → ((p4 ∧ True) → (p1 ∨ p3)))) ∨ False)) ∧ (p1 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63210499671544647017424921414 : ((p5 ∧ ((((p4 ∧ p2) ∧ ((False → (p3 → False)) ∧ ((((False ∧ p4) → p2) ∧ p2) ∨ False))) → p3) → (p5 ∨ (p5 ∧ (True ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711947253311275704555720862310 : ((((((p1 ∧ (p2 ∧ p5)) ∧ p2) ∨ p5) ∨ (((False ∧ (p1 → ((p4 ∧ ((p4 ∨ p2) ∧ (p2 → (p3 ∧ p2)))) → p5))) ∧ p5) → True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51114858421748555607305937049 : ((((((True → (((p5 → ((True ∧ p5) ∧ True)) ∧ False) → (False ∧ p5))) ∧ p4) → p2) ∨ p4) ∨ (p1 ∨ (p4 ∨ ((p4 ∧ p4) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172091967448547217291836491309 : ((((p5 → p3) → ((p4 ∧ ((p4 ∧ True) → False)) ∨ (p5 ∨ True))) → (True ∧ p1)) ∨ (p3 → ((p3 ∧ p1) ∨ ((p3 → (p5 ∧ p5)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62797483042923585864264040621 : ((p4 ∧ (((False ∧ (p2 ∧ ((p4 → (p5 → (True ∧ p3))) → False))) → (False → (p3 ∧ p5))) → (((p5 ∨ p2) → (True → False)) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350005772739012534447993436284 : (p4 → (((p5 ∧ ((((p4 ∨ p5) ∨ (p1 ∧ False)) ∨ False) → (((((True → ((p2 ∧ p5) → p4)) → p4) → p2) → False) → p2))) ∨ True) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60961236467887800244983235432 : ((False ∧ (((((p1 ∨ ((p2 ∧ (p4 → (True ∨ True))) ∧ ((p4 → p1) ∨ p5))) ∧ True) ∧ p4) → (((False ∨ p4) ∧ p2) ∧ p3)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52631274346568347250655368229 : ((((p5 ∨ p5) ∧ ((False ∨ (p2 ∨ (p2 ∨ (p4 ∧ (p4 ∧ p3))))) ∨ p1)) ∨ ((p3 ∨ p5) ∨ ((False → True) ∨ (p4 ∧ (p1 ∧ p2))))) ∨ p2) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



