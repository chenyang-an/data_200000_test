variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354622681833024463665878312905 : (p5 → ((((False ∨ p1) ∧ (((p2 → ((True ∨ p5) ∨ (False ∨ (p3 → p4)))) ∧ False) ∨ (True ∧ (p3 ∧ ((p5 ∨ False) ∨ p3))))) ∨ p2) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675837564649702741111644282373 : (((((p5 → ((p1 ∨ ((False → (True → p5)) → True)) → (False ∨ p1))) ∧ ((False → p1) ∨ (p5 ∨ p3))) ∧ ((p5 → False) ∧ (p3 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186662990877707884577767335914 : (((((p3 ∨ False) → p3) ∧ (p1 → p5)) ∧ ((False → p5) → True)) → (True ∧ ((p5 ∨ ((p4 ∧ True) → ((p1 ∧ p2) → p5))) ∧ (p4 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h6.left
  let h11 := h6.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h12 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h13 := h5 h12
  -- One of the premise coincides with the conclusion.
  exact h13
  -- Implications on the right can always be decomposed.
  intro h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193697609263816988847226057940 : ((p1 ∧ (p3 ∧ (p3 ∨ ((p1 ∧ (p4 ∨ p2)) ∧ p3)))) → ((p5 → (p5 ∧ p2)) → (((p2 ∨ (p3 ∧ p1)) ∧ ((True → p3) → p5)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157993659278071072558869274834 : ((((p3 ∨ (p4 → p3)) → ((True ∧ p3) ∨ True)) → ((((True ∨ (p5 ∧ p1)) → p1) ∧ True) → p1)) ∨ (((p2 → p3) ∨ p5) → (p4 ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (True ∨ (p5 ∧ p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643794137760223111979437423282 : ((((p5 ∧ (((p4 ∧ (p2 ∨ p4)) → (False ∨ p2)) ∨ (p5 ∨ (((p5 → ((True → p5) ∨ (p2 ∨ p5))) ∧ (True ∨ p3)) ∨ True)))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84851948706556993529991765553 : (((p3 → ((False ∨ (((p2 ∧ (p4 ∨ p3)) ∧ p1) → (p5 ∧ True))) ∧ False)) ∧ ((p3 ∧ (((p3 → p5) ∨ p1) ∨ True)) ∧ (p2 ∨ False))) → False) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h10 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h11 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h12 := h2 h11
        -- We need to get the right conjuct of h12 based on <expert-advice>.
        let h13 := h12.right
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h16 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h17 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h18 := h2 h17
        -- We need to get the right conjuct of h18 based on <expert-advice>.
        let h19 := h18.right
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- False on the left can always be used.
        apply False.elim h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h22 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h23 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h24 := h2 h23
      -- We need to get the right conjuct of h24 based on <expert-advice>.
      let h25 := h24.right
      -- False on the left can always be used.
      apply False.elim h25
    case inr h26 =>
      -- False on the left can always be used.
      apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616869591474441561915717856847 : ((((((True → ((p3 ∧ p5) → (p1 ∨ (False ∧ True)))) → p4) → ((((p4 ∨ False) → p5) ∨ ((False ∧ True) → p5)) → (p5 ∨ p4))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_136142618122126181298503184498 : ((((p5 ∧ ((p3 ∨ p3) ∧ p1)) ∧ (p2 ∨ p2)) → ((((((p1 → (p5 ∧ False)) ∨ p4) ∨ p1) ∨ True) ∨ p4) ∨ p1)) ∨ ((p3 ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340889743769588956570692460004 : (p2 → (((((p1 → p1) ∧ ((True → ((p1 ∨ p3) → p1)) ∧ (p5 → p3))) → p2) → ((p1 ∧ ((p3 → p5) ∨ p5)) → (p4 ∧ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696168464185233936964920033944 : ((((p2 ∨ ((((p5 ∨ (False ∧ ((False ∧ p3) ∧ p2))) ∨ p3) ∧ p4) ∧ p4)) → ((p2 ∧ (True ∧ ((False → True) → p4))) → (False ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61327568848555791266237442004 : ((False ∧ (p5 → ((((p2 ∨ (p1 ∧ True)) ∨ p5) → (False ∧ p1)) → ((True ∧ True) ∧ (p1 ∧ (True → (((p1 ∨ p5) ∨ True) ∨ p2))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228763810265300903041800129979 : ((p3 ∨ (p1 ∧ p2)) ∨ (p2 → (((p5 ∨ p4) → ((((True → False) → False) ∧ (False → (p1 → True))) ∨ ((p3 → (False ∨ p5)) → p5))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- False on the left can always be used.
    apply False.elim h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173695982000692533078660292476 : (((((False → (p1 ∨ (p5 → (p3 → p2)))) ∨ (p5 → (True ∧ True))) → p3) ∨ p4) → ((p4 → (False ∧ (p2 ∨ (p2 ∨ p3)))) ∨ (False ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228774804671648115660091821185 : ((p3 ∨ (p3 ∧ p2)) ∨ ((p4 ∧ (p2 ∨ p4)) → (False ∨ (((((p2 ∨ p3) ∧ ((((p5 ∧ False) → False) → p5) → p4)) ∨ p3) ∨ p5) ∨ p4)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179296865235445330522773493307 : ((False ∨ (((p2 → p2) ∧ ((p4 → p1) → ((p2 ∨ p3) ∨ False))) ∨ True)) ∨ (((p3 → (p5 → p3)) ∨ (True ∨ False)) ∨ ((p2 ∨ p1) ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313187774079790029778594684927 : (p3 ∨ (((False ∨ (((False ∨ p5) ∧ p3) ∧ p5)) ∨ (p5 ∨ ((p5 → True) ∨ (False ∧ (((True → p1) ∨ p4) ∨ (p4 ∧ (p5 → False))))))) ∨ p2)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139521496536074558823183214032 : ((((p5 ∨ ((((True → p3) ∧ ((p3 ∧ p4) ∧ (((p4 ∨ p4) ∧ False) → False))) → (p3 → p1)) ∨ p2)) → p4) → p2) → ((p1 → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198070240407482694018558709674 : (((p1 ∨ p2) ∨ (p2 ∧ (p2 → (p4 → p5)))) ∨ (((p3 ∨ (p3 → (True → ((p3 ∧ (p1 ∧ (True → p5))) ∧ p2)))) ∨ (False → p1)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118652472133244944237098206290 : ((p4 ∨ (p3 ∧ ((p4 ∧ (p3 ∧ ((p3 ∧ p2) → (p4 ∧ p1)))) ∨ ((((p1 ∧ p3) ∧ (True → (p1 ∨ p4))) → True) ∨ False)))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2668520017199580835139153391 : ((p3 ∧ ((p4 ∨ (False → p2)) → False)) ∨ (True ∨ ((((False ∨ ((p1 ∧ False) ∨ True)) ∧ p1) → (True ∧ (p2 → p5))) ∨ (p2 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41318996461338299815954384898 : (((((p1 ∨ (p2 → False)) ∨ (p4 → (((p4 ∧ (p5 ∨ True)) → (True ∧ False)) → p3))) ∧ ((p3 ∨ False) ∨ ((p4 → p5) → True))) ∨ p5) ∨ p5) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p4 ∧ (p5 ∨ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140790240741378400207912897944 : (((((p2 → p3) → (p5 ∧ p1)) ∧ (((False ∧ p1) ∧ False) ∨ p1)) ∧ ((((p3 ∨ p5) ∨ p1) → (True ∨ False)) → p3)) → (p1 ∨ (p1 ∧ True))) := by
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
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337536318536174275816016099670 : (p1 → ((((((p2 → (p2 ∨ (p5 ∧ p2))) ∨ p5) ∨ True) ∨ False) ∧ (((p2 ∨ (False → p4)) ∧ p5) → False)) ∨ ((p3 ∨ (p1 ∨ p5)) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184242728144411577197671783596 : ((((((p3 ∨ p2) ∨ True) ∧ (p2 ∧ (p5 → False))) → p2) → False) ∨ (((p3 → (((True ∧ p1) ∨ True) → p2)) ∧ (p1 → p3)) → (p1 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199573295036204347383998803497 : ((((True ∧ (p1 → (p5 → p1))) ∨ p2) → p1) → (((p1 ∨ (p2 → p2)) → p2) ∨ ((((p4 ∨ True) ∨ p2) ∧ p2) ∨ (p4 ∨ (p1 ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∧ (p1 → (p5 → p1))) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636669147560253920873237296582 : (((((((p4 ∧ ((True ∨ (p4 ∧ p1)) → p4)) ∧ p1) ∧ (p4 → (p3 ∨ p4))) ∨ (False → ((p4 ∨ p5) ∨ ((False → p4) ∨ True)))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807396231528042138596398637965 : (((p4 → ((((p2 → False) ∨ ((True ∧ (p5 ∨ p4)) ∧ p4)) ∨ p2) → (((p2 → (p4 ∨ (((p5 ∧ p4) ∧ True) ∧ p3))) ∧ p2) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167695959009798896006515519985 : (((((p1 → False) → ((True → p4) ∧ p2)) → (p5 ∧ (p2 → p5))) ∧ ((p3 ∨ False) ∨ p1)) → ((False ∧ ((p4 ∧ p4) ∧ (True ∨ True))) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157374327940170415847741375774 : (((p5 → ((False ∧ ((p1 ∧ p4) ∨ ((p1 ∨ (p3 → False)) ∧ p1))) → ((p4 → p2) ∧ p4))) → p2) ∨ (p1 → (True ∧ ((False ∨ p1) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_876387233945433875416541330268 : (((((((p1 → (((p1 → p1) ∨ False) ∨ p1)) ∧ (p5 → ((p1 ∧ False) ∧ (False ∧ p5)))) ∧ p5) ∧ (p3 ∧ (True → p5))) ∧ (p1 ∨ p3)) → False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h5.left
  let h11 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h12 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h13 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h14 := h9 h13
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h18 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h19 := h9 h18
    -- We need to get the left conjuct of h19 based on <expert-advice>.
    let h20 := h19.left
    -- We need to get the right conjuct of h20 based on <expert-advice>.
    let h21 := h20.right
    -- False on the left can always be used.
    apply False.elim h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193563699181240501780240898451 : (((False ∨ p2) → (p1 → ((p5 ∧ (p5 ∧ True)) → p1))) → ((p4 ∧ (p3 ∨ (p1 ∨ ((p1 ∧ p3) ∨ p4)))) ∨ ((False ∧ (p1 ∨ False)) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38323821021000409323930316963 : ((((p2 ∨ (p1 ∧ ((p2 → (p4 ∨ ((((p3 ∧ p1) ∧ False) → (p5 ∨ p3)) ∧ p2))) ∨ False))) → ((p3 ∧ (False ∨ p2)) ∨ p3)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797301280371816715747499928590 : (((p1 → (((p5 ∧ ((p2 ∨ p4) → (((False → ((((p1 ∧ p1) ∨ True) ∧ p4) ∧ (p4 ∧ p5))) → p2) ∨ p4))) ∨ (p1 → p1)) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199689526615011460422211880512 : ((((p3 → p1) → ((True ∨ False) ∨ True)) → False) → ((((((False → ((p1 ∨ p5) ∧ p2)) ∨ True) → p1) ∧ True) → p4) → (p3 ∨ (p4 ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p3 → p1) → ((True ∨ False) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191293919889596397937489591620 : (((False → False) ∧ ((p5 ∧ (p2 ∨ p5)) ∨ (p1 → p5))) ∨ (p4 ∨ ((((p4 → (p3 ∧ p3)) → (((p1 → p1) → p5) ∧ p2)) ∨ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57540691217856452505867410498 : ((((True ∧ p5) ∧ p2) → (((p5 → p5) → ((p4 ∨ (p1 ∧ p2)) ∧ ((p3 → p2) ∧ (((False ∧ p2) ∨ (False ∨ True)) ∧ False)))) → p3)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : (p5 → p5) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h7
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709455758816420150428131414561 : ((((p3 ∧ (((False ∧ (True ∧ False)) ∧ p5) ∨ p3)) → ((p1 ∨ (False ∧ p2)) ∧ ((p5 ∨ (p3 ∧ ((p2 ∨ True) ∨ (p4 → p2)))) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807122351144335466723182446348 : (((p4 → (((True ∨ ((p3 ∨ (p3 → True)) ∨ ((p3 → p1) → ((p1 → (p4 → p2)) → p2)))) → p2) → (p1 ∨ ((False ∨ p1) ∨ p2)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ ((p3 ∨ (p3 → True)) ∨ ((p3 → p1) → ((p1 → (p4 → p2)) → p2)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10146825576752949920708077485 : (((False ∨ ((False ∧ (True ∨ (True ∨ p4))) ∧ (p1 ∨ (((p5 ∧ (((p3 ∧ p4) ∧ p5) ∨ p4)) → p5) ∧ (p1 ∨ (p3 → p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172429110613699152759071216465 : (((p5 ∧ (p5 ∨ (False ∧ p5))) ∧ ((p5 ∧ (p5 → (p1 → (p1 → p2)))) ∧ p3)) ∨ ((p4 ∧ (p1 → (True → ((True → p3) ∧ p1)))) → p4)) := by
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
theorem thm_5_vars_264886979480683852750209267966 : (True ∧ ((p3 → p2) ∨ ((((((p4 → (False ∨ p2)) ∨ ((p4 ∨ (False ∧ p3)) → (p2 ∨ True))) ∨ p4) → (p5 ∧ False)) ∧ (p5 ∧ p5)) → p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (((p4 → (False ∨ p2)) ∨ ((p4 ∨ (False ∧ p3)) → (p2 ∨ True))) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
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
      -- False on the left can always be used.
      apply False.elim h10
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h12 := h2 h6
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746778067907163014068048887611 : ((((p3 ∨ p4) → (((p2 ∨ (((p3 ∧ False) ∨ (p3 ∨ p2)) ∨ (((((p3 ∨ p2) ∧ p1) ∧ p1) → False) → p4))) ∧ p5) → (p4 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234637160365679515757147732962 : ((p3 → (p3 → True)) → (((p3 → False) ∧ (True → (p1 ∧ (((False ∧ True) ∧ False) ∧ (p2 ∧ p1))))) ∨ (False → (p5 ∨ ((p2 ∧ p1) ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40146419433876546953984999141 : (((((p2 ∧ (((True → (p4 ∨ p3)) → ((False ∧ (p1 → True)) ∧ p5)) ∧ p3)) ∨ (p3 → (((p4 ∨ False) ∨ p2) ∨ False))) ∧ p1) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133388545984322618207118384225 : ((p4 → ((False ∧ (p2 ∨ (p5 → (p4 → ((p3 → (p4 → (((p3 → p1) → False) ∧ (True ∨ True)))) ∧ p3))))) ∨ True)) ∧ (p4 → (p3 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49145869352950540225459560891 : (((((p5 → p5) ∨ (False ∧ (p3 ∧ ((p5 → p2) → False)))) → (p4 ∧ (((p3 ∨ (p2 ∧ p2)) ∧ p3) ∨ p3))) ∨ ((p1 ∨ p1) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54665574970187865732636625077 : ((((p5 ∨ (False ∧ ((False → p5) ∧ p3))) ∨ p2) → ((False ∨ ((p1 ∧ (p1 ∧ (p4 ∧ p3))) ∨ False)) ∨ (((p4 ∨ False) ∧ p2) → p4))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244781802148849697435855528002 : ((p1 ∧ False) ∨ (p4 ∨ (((p5 → ((True ∨ p2) → (True ∧ (((False ∧ p1) ∨ p1) → p4)))) ∨ (p3 ∧ ((p4 → True) ∨ p2))) ∨ (False → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113590711315547185189738279144 : (((p4 ∧ ((p2 ∨ p1) ∧ ((p1 → ((p2 ∧ ((p1 ∧ (p3 ∨ False)) → p4)) ∨ False)) → ((True → p2) ∨ p5)))) ∨ (p2 ∨ p2)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62744431437164237110324553089 : ((p4 ∧ ((p4 ∨ (p1 ∧ ((((True ∧ p5) ∧ ((p5 ∨ p1) → (False → (p2 ∨ p3)))) → ((False ∨ p2) ∨ False)) → p4))) ∨ (p2 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7738407893809374487109974528 : (((((((((False ∧ ((p3 → False) → (p3 → p4))) → ((True → True) → p3)) ∧ p1) ∨ (p1 ∧ p2)) ∨ p3) ∧ (p2 ∧ p4)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114944893040049745522720716762 : ((((p5 ∧ p3) ∧ (p1 ∨ ((p5 ∧ p2) → (((p5 → p5) ∨ p3) ∨ p4)))) → ((p1 → p4) ∧ ((p3 ∧ (p3 → p3)) ∨ p1))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746840208077150817439557274051 : ((((p3 ∨ p5) → (True → (((p3 ∨ (True → (p2 ∧ (p5 ∨ p3)))) ∨ True) → (((p5 ∧ (p1 → True)) ∨ (p1 ∧ p3)) ∨ (p3 ∨ p4))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
        exact h5
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h14
      -- Implications on the right can always be decomposed.
      intro h15
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595978994588717193218451476055 : (((((True → ((p1 → (((p2 ∨ False) ∧ p3) ∧ p4)) ∨ p4)) ∨ ((((p5 ∨ p2) ∨ ((p4 ∧ p2) ∧ p2)) ∧ (p4 ∨ p1)) ∨ p2)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111117390844639327441527996622 : ((((p5 ∧ ((p3 ∨ (p1 → ((p3 ∧ p1) ∧ p4))) ∨ False)) → ((p5 ∨ ((p1 → p1) ∧ (p4 → (p3 ∧ p5)))) → False)) ∧ p3) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347636428945050916082985979123 : (p3 → ((((p3 ∨ True) ∨ p3) ∧ p5) → (((p4 ∧ (((p1 → (((False ∨ True) ∨ p4) → (p1 ∨ p3))) ∧ (p4 → p3)) → False)) ∧ p1) ∨ p3))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186054772122030771407788016380 : (((((True ∨ ((True → (p3 ∨ True)) ∨ False)) → p1) ∨ p3) ∨ p1) → ((p1 ∧ (((p4 ∨ (p1 → (p1 → True))) ∧ (False ∨ True)) ∨ True)) ∨ p3)) := by
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h4 : (True ∨ ((True → (p3 ∨ True)) ∨ False)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h5 := h3 h4
      -- One of the premise coincides with the conclusion.
      exact h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651060603845563032333008439993 : ((((((p3 ∨ p4) ∧ (p3 ∨ p5)) ∧ (((p5 ∧ (((p1 → (False ∧ False)) ∧ p4) ∨ p2)) ∨ ((p2 ∧ p1) ∨ False)) ∧ p2)) ∧ (False ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47238672624967207371491862211 : (((((((p1 ∨ True) ∧ p5) ∨ p1) ∨ (p3 ∧ True)) → (((p4 ∨ p5) → (((p2 → False) ∨ p5) → True)) ∧ (p1 → False))) ∨ (p4 ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42433066420818018689972583511 : (((p5 ∧ ((p1 → p5) ∧ ((p4 → (((p5 ∧ False) → p3) ∧ p4)) → (((p4 → True) ∧ (p4 ∧ (False → (True ∧ True)))) → False)))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257444085398533537507346917924 : ((p3 ∨ True) → (((True → ((p3 ∧ ((p5 ∧ True) ∧ p4)) → (p3 ∨ (((p5 → (p3 ∨ p4)) ∧ p1) → p2)))) ∨ p1) → ((p3 → p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
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
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113549759426565585425439617076 : ((((False ∨ (p2 ∨ p1)) ∨ (((p4 → (p5 ∨ p3)) ∨ (True → p4)) ∧ ((p3 ∧ p4) ∧ ((p3 ∧ p5) ∧ p3)))) ∨ (p4 ∨ p2)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61674741168912523167161877357 : ((p1 ∧ (p5 ∧ ((p2 ∧ p1) ∨ ((p1 ∧ ((p5 ∨ True) ∨ True)) → ((p3 ∧ (p4 ∧ ((p5 ∧ p3) ∨ (p2 → (True ∨ p4))))) ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191111866263396809642973624403 : (((p5 ∧ (p3 ∧ p5)) ∧ ((True → (p4 → p1)) ∨ p4)) ∨ (p4 ∨ ((True ∧ False) → ((p5 ∧ (p2 ∧ (((p3 ∧ p5) ∧ False) → True))) ∨ False)))) := by
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
theorem thm_5_vars_93804209079566319099293763490 : ((p1 ∧ ((p2 ∨ ((p4 → p5) ∨ (((p1 → (p2 ∨ (p5 ∨ (p4 → (((p5 → (p3 → p1)) ∧ p2) ∨ False))))) ∧ p5) ∨ p1))) → False)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p2 ∨ ((p4 → p5) ∨ (((p1 → (p2 ∨ (p5 ∨ (p4 → (((p5 → (p3 → p1)) ∧ p2) ∨ False))))) ∧ p5) ∨ p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599996327617835175753697072017 : (((((False ∨ True) → (((p2 ∧ ((p2 → p1) ∨ p2)) ∨ (False ∨ (p3 ∨ (True ∨ (True ∨ p4))))) → ((p5 ∧ (False ∨ p3)) ∧ p4))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213513568422198742161096077501 : (((p4 → (p1 ∨ p3)) ∧ p4) ∨ (((p4 ∨ ((((p4 → True) → ((p5 ∨ (p4 ∧ (p3 ∧ p5))) → (p2 ∨ p1))) ∧ True) ∨ False)) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788949563962638944714912592445 : (((p5 ∨ ((((p2 ∧ p3) ∧ (((p4 ∨ False) ∧ p2) ∨ (p1 ∧ p1))) ∨ ((True ∧ p5) → (False ∨ ((False ∧ p1) → True)))) ∨ (p5 ∨ p4))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355853874297571558860572151595 : (p5 → ((((False → (p5 → (p1 ∧ (p1 ∨ True)))) → (p3 ∨ (((p2 → False) ∨ p5) → p3))) ∨ ((p1 ∨ p5) ∨ False)) ∨ (False → (p1 ∧ False)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_819222150219365828724088587868 : ((((((((p2 → (p4 ∨ (p2 ∨ p4))) → (((p2 ∨ p4) ∧ ((p4 → p3) → p3)) → False)) ∧ p2) ∧ p3) ∧ ((p3 → p1) ∧ p5)) ∧ p1) → p4) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h5.left
  let h11 := h5.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h12 : (p2 → (p4 ∨ (p2 ∨ p4))) := by
    -- Implications on the right can always be decomposed.
    intro h13
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h14 := h8 h12
  -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
  have h15 : ((p2 ∨ p4) ∧ ((p4 → p3) → p3)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
    -- Implications on the right can always be decomposed.
    intro h16
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h14, we can now drive its conclusion.
  let h17 := h14 h15
  -- False on the left can always be used.
  apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68668777006167091042123570673 : ((p4 → ((False ∨ (True → ((p5 → ((False → ((p3 → (True → p2)) ∧ (p5 ∧ (p5 ∧ False)))) → ((True ∨ p4) ∨ True))) → p3))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114737116249512500230016084898 : (((((p4 → p2) ∧ p2) ∧ (((p3 ∧ (p5 ∨ p5)) ∧ True) ∨ (p2 ∨ (True ∧ p5)))) → ((p3 ∨ p4) → (p3 ∨ (p3 ∧ p2)))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47687884970636842673422255001 : ((((p4 ∧ (False → (False ∨ (p2 → (((p4 ∨ (p1 ∨ False)) ∨ (True ∨ True)) ∨ (((p1 ∧ False) ∨ p1) ∧ False)))))) ∧ True) → (False ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199840900416667240945061499236 : (((True ∧ ((p4 → p2) ∧ p4)) ∧ (True ∧ p4)) → (p2 → (p5 ∨ ((p5 → (p1 ∨ ((p2 → False) ∨ ((p1 ∨ p4) ∨ True)))) ∨ (False → p3))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h4.left
  let h10 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h11
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761788661316520077574940539178 : (((p3 ∧ (((((((p4 → (p3 → p1)) → ((p2 ∨ (p3 ∧ False)) ∨ p4)) → True) ∨ True) → (((p2 → False) ∨ p3) ∨ p2)) ∧ p5) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318565755446527993364613521834 : (p4 ∨ ((((((((p1 → p2) ∨ ((p4 ∨ ((p4 ∧ p5) → p3)) ∧ (p2 ∨ p1))) ∨ p5) ∨ (p1 ∨ True)) ∧ p5) → p4) → False) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625203928471081017926962916045 : ((((True → ((p1 ∨ p2) ∨ (p3 → (p5 ∧ (((p5 ∧ p4) ∧ (p2 ∨ (True ∧ ((False → False) → p3)))) ∨ (p3 ∧ (p5 ∧ True))))))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_43525108115117398577694356974 : ((((True → ((p5 ∨ (True ∧ p2)) → ((True → (p3 ∧ p1)) ∨ ((False ∨ (((p4 ∨ p5) ∧ (p4 ∨ p2)) ∧ p4)) ∨ False)))) ∨ False) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57605000930145188208164654010 : ((((p3 → p2) ∧ True) → (((((True ∧ p3) → p5) ∨ (((p2 ∧ ((((p3 ∧ p3) ∧ False) → p3) ∧ p3)) ∧ p5) ∨ True)) ∧ p1) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64266051214433262190968678814 : ((False ∨ (p5 ∨ (p5 ∨ (True ∧ (((p4 ∨ (p3 ∧ (p4 ∨ p5))) → ((True ∨ True) ∧ (((False ∨ (False ∨ False)) ∨ True) ∨ p3))) ∨ p5))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
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
theorem thm_5_vars_321260012367681825616163784946 : (p4 ∨ (p4 ∨ (((p5 ∧ (p2 → True)) ∨ p3) ∨ ((p2 ∧ p3) ∨ (((p2 → (True ∨ ((True ∧ (p2 → p2)) ∨ (p2 ∧ p1)))) → False) ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197324484364950637002096168976 : ((((True ∧ p5) → (True ∧ (p4 → True))) → p3) ∨ (((p5 ∧ p1) → ((((p4 → p2) → p4) ∨ ((False → p2) ∧ True)) ∨ (p4 ∧ True))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1780609600063730747138744623 : ((((p1 → (False → p3)) → (((((p2 → (p2 ∨ p5)) → (p2 → True)) ∧ False) ∨ p5) ∧ p2)) → (p3 → p1)) ∨ ((p1 ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186190506638020347990790065155 : (((p5 ∧ (False ∨ (p4 ∧ (p4 ∨ ((True ∨ p1) ∧ p4))))) ∨ p1) → ((p4 → False) ∨ ((((p2 → p4) ∨ p1) ∨ p5) ∨ ((p4 → True) ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60455165003573287975353974276 : (((p5 → p1) → ((((False → p2) → False) ∧ p3) → (((p5 ∨ p3) ∧ (p1 ∧ ((p1 → (True → p4)) → p2))) ∧ ((p2 ∨ p3) ∨ p4)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : (False → p2) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h7
  -- False on the left can always be used.
  apply False.elim h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h2.left
  let h12 := h2.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h13 : (False → p2) := by
    -- Implications on the right can always be decomposed.
    intro h14
    -- False on the left can always be used.
    apply False.elim h14
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h15 := h11 h13
  -- False on the left can always be used.
  apply False.elim h15
  -- Conjunctions on the left can always be decomposed.
  let h16 := h2.left
  let h17 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135775663537428294739694239307 : ((((p5 → (True → (((p5 → ((p5 → p5) ∨ p5)) ∨ p2) ∨ False))) ∨ p2) → (((p1 ∧ p3) ∨ False) ∧ (p3 → p1))) ∨ ((p4 ∧ p3) → p3)) := by
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
theorem thm_5_vars_198980769119965233904896995474 : ((p5 → ((p1 → (p1 ∨ p1)) → (p4 ∨ p1))) ∨ ((False ∧ p4) → ((((p4 ∨ (False ∧ False)) ∧ ((p4 ∨ (p1 ∨ p1)) → p1)) ∨ p3) → p4))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h1.left
      let h8 := h1.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198759479018045450263770222743 : ((True → ((p3 ∨ p4) ∨ ((p5 → p3) ∨ p5))) ∨ (p3 → (((p1 ∧ (p3 → p3)) → ((True ∧ ((False ∧ p3) ∧ p1)) ∨ True)) ∨ (p3 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38419971439620487213027863535 : ((((False ∧ ((p1 → (p3 → ((False ∧ p1) ∧ ((p3 ∧ p5) ∨ False)))) → p3)) ∧ (((p2 ∨ True) → (p2 → p1)) → (True ∧ True))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148791968874946843103164763999 : (((p5 ∨ (p1 ∨ ((p5 → p3) ∨ p2))) ∨ (((p3 → (p2 ∨ ((p3 → False) ∨ False))) ∨ (p1 ∨ p1)) → p2)) ∨ ((p4 ∨ True) ∨ (p1 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158873285260351002486493511968 : ((False ∨ (((p5 ∧ (p2 → p1)) ∧ p3) ∨ ((p4 ∨ (((p2 → p3) ∧ p1) ∧ p2)) ∧ (False ∨ p3)))) ∨ ((p1 ∧ True) → ((p3 → True) ∨ True))) := by
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
theorem thm_5_vars_767745842141738174472231118960 : (((p5 ∧ ((((True → p1) ∧ ((((True → ((p1 → (p1 ∨ False)) ∨ p3)) ∨ ((p2 ∧ p5) → False)) ∨ p5) ∨ (p5 ∨ True))) ∧ p4) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609701572500507211039887468407 : (((((p2 ∨ (((p3 ∧ (p1 ∨ ((p3 ∧ p4) ∨ (False → True)))) → (True → p4)) ∨ ((p1 → ((p5 → True) → p3)) ∨ p1))) ∨ True) ∨ p2) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60220715448583595150789669657 : (((True → p1) → (p4 ∨ (p3 ∨ ((((True ∨ ((p1 → (p5 ∧ (((True ∨ p3) ∨ p5) → True))) ∧ p1)) ∧ True) ∧ (p3 ∨ p1)) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309618917157321152689090500465 : (p2 ∨ (((((((p3 ∨ p5) → p1) ∧ (p4 ∧ p3)) ∨ (p3 → ((p5 ∧ p5) → p2))) → (p2 ∨ p2)) ∨ (False → True)) ∨ ((False → p4) ∨ p5))) := by
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
theorem thm_5_vars_230014575713142045194297012059 : (((p1 ∧ True) ∧ p5) → (p4 → ((((True ∧ (((p1 ∨ False) ∨ p3) → (True → (p1 ∧ p1)))) ∧ p2) → ((p3 → p2) ∧ p3)) ∨ (False → p2)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356953904203717160383409417296 : (p5 → (((False ∨ True) → True) ∧ (((((True → False) ∨ False) → True) → p2) ∨ (p2 ∨ ((p2 → False) ∨ ((p1 → ((False → True) → p5)) → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166787515457635023871774393796 : ((p5 → (p2 ∧ (True → ((((p1 → True) ∨ (p1 → (False ∨ p3))) → (p3 ∨ False)) ∧ p4)))) ∨ ((True ∨ True) ∨ (((p5 → True) ∧ True) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81233757215491103362494549443 : (((True → (((p1 ∧ (((p2 → (False ∧ p1)) ∨ ((p1 ∨ ((p2 ∨ p1) ∨ p1)) ∨ True)) ∨ p5)) → p1) ∧ False)) ∧ (p2 → (True ∧ True))) → p3) := by
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
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



