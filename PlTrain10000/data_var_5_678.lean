variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60442388662933984323120680085 : (((p5 → True) → (((p2 ∧ (((p3 → (True ∧ p1)) ∧ (p4 ∧ (((p5 ∧ p5) ∧ p4) ∨ (p3 → True)))) → False)) → p4) ∨ (p2 → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336235104955893599126088659446 : (p1 → (((p3 → ((False → ((True → (False → (False ∨ (p3 ∧ (p3 ∨ p5))))) ∧ (p3 → False))) ∨ (p2 ∨ p5))) → ((p5 ∧ p1) ∧ p1)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358155085792207089937492405764 : (p5 → (p3 ∨ ((((p5 ∧ (((p4 → p5) ∨ (p2 ∨ p3)) ∧ ((p5 ∧ (p3 → (p5 ∨ False))) → (p5 → (p4 → p4))))) ∨ p5) → p1) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149185882630063084827115331104 : (((p1 → p4) ∧ ((True ∧ p2) ∧ (((p1 → p2) ∨ True) → ((True ∨ ((p3 ∨ p1) → p1)) ∧ (p2 → p3))))) ∨ (((p2 ∨ p2) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603176181250951709470247703756 : ((((p2 ∨ ((((((p4 ∧ (p1 → (p1 → ((True ∨ ((p3 → False) ∧ p3)) ∨ True)))) ∧ p4) ∨ p4) → True) ∧ p5) → (p5 → p1))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49953940066484680783157725102 : (((((True → ((((p3 → p4) ∧ p1) ∧ ((p5 ∨ p3) ∨ False)) ∧ (p3 ∧ p4))) ∧ p2) → (p3 ∨ False)) ∧ (((p4 ∨ p3) ∧ p4) → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41024504328467292649745617980 : (((((((False → p3) ∧ (((p1 ∧ ((p5 ∧ False) ∨ (p2 ∨ p1))) ∧ p3) ∨ (p1 → p5))) ∧ p5) ∧ (p1 ∨ p5)) → (p3 ∧ p5)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647512108297388543893593048811 : ((((p5 → (((p2 ∧ ((p1 ∨ ((p1 ∧ p3) ∧ ((p5 ∧ True) ∧ p4))) ∧ p5)) ∨ (((p5 ∨ p1) → p4) ∨ (p5 ∨ True))) ∧ True)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60335769443320608937437157539 : (((p2 → p1) → ((p1 ∧ ((((p4 ∧ (False ∧ (p5 → (True ∧ p3)))) → (p2 ∧ p5)) → (False → p3)) ∨ (p2 ∧ p3))) → (False ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9242927514005246923295287707 : ((((((p3 → (p4 ∧ p1)) ∨ p4) → (p3 ∨ p5)) ∨ (p2 ∧ (((p2 ∨ p1) → p2) ∧ ((((p1 ∨ p4) → True) ∨ p2) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115123646020383450655546808193 : ((((((p3 → p3) ∨ (p2 ∧ p2)) ∨ p1) ∨ ((p1 ∧ p4) ∧ p3)) → (((True → ((p5 ∨ False) → p5)) ∧ (p1 ∨ p4)) ∨ p1)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54271149172151258756308673284 : ((((p4 ∧ (False ∨ False)) ∧ (p1 → (True → p4))) ∧ ((((p1 ∨ (p3 → (True ∨ True))) ∧ (p1 → True)) ∧ (p4 → (p2 ∧ p5))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193440742021251180776605550138 : (((p1 → p2) ∧ (((p5 → (False ∨ False)) ∨ True) → False)) → (((True ∨ False) → p3) → (p5 ∨ ((p3 ∨ (p2 → (p5 → (False ∨ p4)))) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((p5 → (False ∨ False)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306170877699450743780263432221 : (p1 ∨ (((p1 → p1) → p1) ∨ ((((p5 → (p2 ∧ ((((p4 ∨ p2) ∨ (p5 ∨ p5)) ∨ False) ∧ (False ∧ False)))) ∧ (False ∨ False)) ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133666857616454460612914538808 : (((((p3 → (((((False ∨ (p3 → p5)) ∧ p3) → (True → False)) ∨ p2) ∧ (True ∨ p3))) ∧ True) → (p5 ∨ p4)) ∧ p1) ∨ (False → (p2 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684502722798743400764107353227 : ((((((True ∨ p4) ∧ (p2 → (True → p4))) ∨ ((p3 ∨ (p5 ∧ (p2 ∧ (p2 ∨ p2)))) ∨ False)) ∨ (True ∨ (((False ∧ p2) ∨ False) → p3))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_41650277860786990134509702842 : (((((p1 ∧ (p1 ∨ p2)) ∨ (p4 ∧ p2)) ∧ (((((p4 → p5) ∧ (p1 → ((p2 → (p1 ∧ p5)) → p1))) ∧ p4) → True) ∨ p5)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312733176806192459397957675274 : (p3 ∨ (((((p1 ∧ (p2 ∧ False)) ∧ p4) ∨ (True → (p5 → (False → p1)))) ∨ ((p1 ∨ ((p3 ∧ p3) → (p3 → True))) ∧ (p2 ∨ p4))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_184128704127951101355944635414 : (((p1 ∧ (((p5 ∧ True) ∨ (p2 ∧ p3)) ∨ (p5 ∧ True))) ∨ True) ∨ ((((p2 → ((p3 ∨ p4) ∨ ((p2 ∧ False) ∧ True))) → p5) → p2) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164777110160332445413378295663 : (((((p5 ∨ (p5 ∧ (p3 → False))) ∧ True) ∧ (((p5 → (False ∨ True)) ∧ True) ∧ p5)) ∨ p1) ∨ (True → (False → (False ∧ (p5 → (p3 ∧ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159027148854722026769092777162 : ((p4 ∨ ((False ∨ p5) ∨ ((((p4 → p2) ∨ p5) ∧ p1) ∨ (((p3 ∨ p2) → (True → False)) ∧ False)))) ∨ ((p5 → (p1 ∧ p4)) → (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358054490061056902121422888444 : (p5 → (p1 ∨ ((False ∨ ((p3 ∨ (p3 ∧ p4)) ∨ ((p4 ∨ ((p1 ∨ p4) ∨ True)) → (p3 ∨ p3)))) → (p3 ∧ (((p1 → p1) → False) → p4))))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h10 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h11 : (p4 ∨ ((p1 ∨ p4) ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h12 := h10 h11
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h14
  -- Implications on the right can always be decomposed.
  intro h15
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h16 =>
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
        have h20 : (p1 → p1) := by
          -- Implications on the right can always be decomposed.
          intro h21
          -- One of the premise coincides with the conclusion.
          exact h21
        -- We have shown the premise of h15, we can now drive its conclusion.
        let h22 := h15 h20
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- One of the premise coincides with the conclusion.
        exact h25
    case inr h26 =>
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h27 : (p1 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h28
        -- One of the premise coincides with the conclusion.
        exact h28
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h29 := h15 h27
      -- False on the left can always be used.
      apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607530603574781985642745573015 : (((((False ∧ ((((((p5 → p4) ∨ ((p1 ∨ p2) ∧ True)) ∨ (True → p5)) ∨ (p5 → p2)) → (p4 → (p3 ∨ True))) ∧ True)) ∧ p2) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_232523882732478140741868617363 : ((True ∧ (p5 → False)) → ((p2 → p1) → (((p4 → (p4 ∧ ((False ∨ ((False ∧ p3) → p3)) ∧ (p4 → (p5 → True))))) → False) → (True → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : (p4 → (p4 ∧ ((False ∨ ((False ∧ p3) → p3)) ∧ (p4 → (p5 → True))))) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h14 := h3 h7
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55444397774144178012102212267 : (((((p1 ∨ False) ∧ (False ∨ True)) → p4) → ((p1 → ((p2 ∨ ((p5 → p2) ∨ (((p1 → p5) → (False ∧ p3)) → p4))) ∨ p5)) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157107019688151763593702108714 : (((p3 → (p2 ∨ (True → (((p4 ∧ True) ∨ p5) → ((p4 ∨ (p5 → (p5 ∨ p2))) ∧ p2))))) ∨ p2) ∨ (((p2 → p4) ∨ (p2 ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110838371510400492217713535240 : ((((p1 ∨ ((True ∧ p3) ∨ (False ∨ (((((p5 ∧ (p3 → p5)) ∨ p1) → p5) → (False ∨ (p5 → p5))) → p2)))) ∨ True) ∧ p5) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694798024877595759427997586561 : ((((True → (p3 ∧ ((((p2 → (p1 → p2)) ∧ p1) ∨ (p5 ∧ p3)) ∧ p5))) ∨ ((p4 ∨ p5) ∨ (((p2 ∨ p4) ∧ False) ∧ (False ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606816519966680627688521832276 : (((((((((p5 → True) → (p1 → (p4 ∧ ((p3 → p5) ∧ (False ∧ p3))))) → p1) ∧ (p3 → p4)) ∧ (p3 ∧ (p5 → False))) ∧ p5) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655937134150397144817068843553 : ((((((p4 → (p2 ∧ (p4 → p5))) → (p1 → ((p1 ∧ ((True → p2) ∨ p1)) ∨ p3))) ∧ (((False ∧ p4) ∧ p1) ∨ p5)) ∨ (True → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703179715481299432606753715283 : ((((True ∧ ((p5 → (((p4 → p2) ∨ p2) ∨ p1)) → p1)) ∨ (((p5 ∧ (True ∧ (p2 ∨ (False ∧ (p5 ∨ True))))) → False) → (p4 → True))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116135521484671562331511721970 : (((p3 ∧ (True ∨ p3)) ∧ ((p1 ∨ (True ∧ p2)) ∨ (((True → p1) → (False ∧ (((True → False) → p1) → p4))) → (p3 → False)))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201279739469231681509914371118 : ((p4 → ((((p2 ∧ p1) ∨ p3) ∧ p3) ∧ p5)) → (p5 ∨ (p4 → (((True → ((p3 → ((False ∧ p2) ∨ p2)) ∧ (p3 ∧ p5))) ∨ p2) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h10 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h10
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722342473426806958084810143154 : (((((p2 ∧ p4) ∧ p4) ∧ (((p4 ∨ (False → p1)) ∨ p3) ∧ (((p3 ∨ p4) → ((p1 → (p5 → True)) → True)) → ((p1 ∧ p4) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609109065344168836780800920691 : ((((((p1 ∨ (p3 ∨ (False ∧ (p2 ∨ p4)))) ∨ (True ∨ (p5 ∨ (p5 → (((True ∨ True) ∨ False) → (p5 ∧ (p4 ∧ False))))))) ∨ p4) ∨ p3) ∨ p4) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65029844017266166361108189502 : ((p2 ∨ ((p4 ∧ p1) → (((((p5 ∧ p3) ∨ ((p4 ∨ (False → (True → (False ∧ p1)))) ∨ (p1 → False))) → p3) ∨ (p3 ∨ p5)) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116895938345917720742747835333 : (((p4 → p2) ∨ (p4 ∨ (((p2 → True) → ((p1 ∨ p1) ∨ ((p5 → p3) ∧ ((False → (p5 ∨ p2)) → p1)))) ∧ (False ∧ True)))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704323353609870095559352483351 : (((((True ∧ ((False ∧ p1) ∨ p2)) ∨ (p2 → (False → False))) → (((((p3 → False) ∨ ((False ∨ p4) ∨ p1)) → (p2 ∨ p2)) ∨ True) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64633078012628500792042104073 : ((p1 ∨ (p2 ∧ ((((p2 ∨ p4) ∧ p2) ∧ p3) ∨ ((False ∧ (p3 → p5)) ∨ (((False → (((p1 ∨ True) ∨ p3) → p2)) ∧ p2) ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305184528827330671610957704279 : (p1 ∨ (((p5 → p5) ∧ (((((p5 ∨ p3) ∨ p5) → (p1 ∧ (False ∧ False))) ∨ p2) ∨ ((p5 ∧ p1) ∨ p5))) ∨ (((p3 ∨ False) ∨ p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118132495750384617122943414809 : ((False ∨ (((p5 ∧ ((p1 ∧ p5) ∨ ((True ∧ (p1 ∨ ((False ∨ p4) ∨ (False → p5)))) ∧ p1))) ∨ False) ∨ (p1 → (p4 → False)))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49331013443540284186178172616 : (((p5 ∨ ((p1 ∧ ((False ∨ (((p1 ∨ (p2 ∨ p1)) ∨ ((True ∨ False) ∧ p1)) ∧ p2)) ∧ p1)) ∨ (p5 → p5))) ∨ ((p1 → p3) ∨ p3)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_255137944395348660335922458676 : ((p4 ∧ p3) → ((((p2 ∨ ((p4 ∧ (p5 ∨ p3)) ∨ ((p2 → (True → True)) → p3))) ∨ p1) → (p2 ∧ p2)) ∨ (p2 → (p3 → (False → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115964557954974562818640406429 : (((((True → p5) ∧ p5) ∧ p1) → ((p4 → True) ∧ (p2 ∨ ((p1 → p1) ∧ ((((p5 ∨ p2) → p4) ∨ (p2 → p3)) ∧ p2))))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186239163840722792217070473866 : (((((((p2 ∨ p4) ∧ p1) ∨ (p1 → True)) ∨ p2) ∧ True) → p2) → ((((((p2 ∧ p4) → p2) → False) → (p2 ∧ (p1 → p3))) → p1) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p2 ∨ p4) ∧ p1) ∨ (p1 → True)) ∨ p2) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340922316959808329365093078115 : (p2 → (((p4 ∧ (p3 ∨ (p3 ∨ (p2 ∨ p3)))) ∧ ((p4 ∨ ((p2 → ((p5 ∧ p3) ∨ (p3 → p1))) → (p4 → False))) → (p3 ∧ True))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112867721340428991622861196525 : (((((True → True) ∧ p4) → (((p4 ∧ p3) ∧ (p5 ∧ ((p5 ∨ ((False → (p4 ∨ p4)) ∨ (p3 → True))) ∨ p1))) ∨ True)) → p4) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116337720387726602933853226468 : ((((p3 → p4) ∧ p5) → (((True → ((((p5 → p5) ∧ p5) ∨ (p4 ∨ True)) ∧ p5)) ∧ p4) → ((True ∧ (p5 → False)) ∨ p3))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114630714584778520909474433589 : (((((p3 ∧ p1) ∨ ((p4 → p4) → (p3 ∧ (((p2 → p3) ∧ False) → True)))) ∨ True) ∨ (p2 ∧ (((p1 ∧ p1) → p3) ∨ p2))) ∨ (p2 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193339207489822693636902415560 : ((((p5 ∧ p4) ∨ p5) → (((p2 ∧ True) → p1) ∧ False)) → (((p4 → False) ∨ ((p4 ∧ (p2 → ((False ∨ True) ∧ p3))) ∨ True)) ∨ (p5 → p2))) := by
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
theorem thm_5_vars_351739045444689848912230791582 : (p4 → ((p1 ∧ (((p5 ∧ (False ∨ p5)) ∨ ((p5 ∧ p1) ∨ (True ∧ p4))) ∧ p2)) ∨ ((p4 ∨ p1) → (p3 ∨ ((False → (False ∨ p2)) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613272442583976725855896985926 : (((((((((True ∧ p2) ∨ p1) ∨ p3) → p3) ∨ ((p5 ∨ (p4 ∨ (p5 ∧ (p1 ∧ p5)))) → (True → (True ∧ False)))) → (p5 ∧ p4)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592084028935527135169229031986 : (((((p3 ∨ (p2 ∧ (((p4 ∨ (((False ∨ (p4 → True)) ∧ p4) → p4)) ∨ (p4 ∧ ((p3 ∧ p2) ∧ p5))) ∧ True))) ∨ (p1 ∧ p3)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112627627453868646349402495965 : ((((((p5 ∨ False) → (p4 ∧ (((False ∧ ((p1 ∧ ((p3 ∨ p3) ∧ False)) ∧ True)) ∧ p2) → False))) ∨ p3) → (p4 ∨ p5)) → p1) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38515434185467084762864203480 : (((((((((p3 → False) ∧ (True → p3)) ∧ p4) ∨ p2) → p1) ∨ p3) → ((p1 ∧ (((p4 → False) ∨ True) ∧ (p1 → p4))) ∨ p1)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350941049863515652231521462985 : (p4 → (((((p5 ∧ p1) → p5) → (p4 ∧ (((p3 ∧ p2) ∨ (p4 ∧ p4)) ∧ ((p1 → (True ∧ p2)) ∧ p5)))) ∨ (p1 ∧ False)) ∨ (p4 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116862161568839588310463647762 : (((p1 → p2) ∨ ((p3 ∧ ((((p5 ∧ (p3 ∧ (p2 ∨ p4))) ∧ p4) ∨ (p1 ∨ False)) ∧ p3)) ∨ ((p4 ∧ (p5 ∧ p4)) → p3))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321762992380673619101715897050 : (p4 ∨ (p5 → (p2 ∨ (True ∧ ((p1 ∨ True) → (True ∧ (((p5 ∧ p1) ∨ ((p1 ∧ (p1 ∧ p4)) ∨ p5)) ∨ (p5 ∨ (p4 ∧ (p1 ∨ p3)))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633907686461791475725724895862 : ((((((p4 ∨ ((((False ∨ p4) → p4) → p3) → ((True → (p4 ∨ p3)) → ((p5 ∨ p4) ∧ (p4 → p4))))) ∨ True) → (p1 → p3)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119349643848918780091969095985 : ((p3 → ((p5 ∨ p2) ∨ (((p3 ∧ (((True ∨ False) → (((p3 → (p1 ∨ True)) ∨ p2) ∧ p2)) → p4)) ∨ p1) ∧ (p2 ∧ p5)))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138031117403999262392581958140 : ((True → (((p4 ∨ (True ∧ ((p2 ∨ (p2 → (p3 → True))) → p2))) ∨ ((True ∧ p2) ∨ True)) ∧ ((p1 → p2) ∧ True))) ∨ (False → (p2 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204239295760928198325481255193 : ((((p5 ∧ p3) ∧ (p5 ∨ p1)) ∧ p5) ∨ (p1 → ((((p2 → (False ∨ True)) → p3) ∧ (p2 ∨ p4)) → (((False ∨ p1) ∨ (p4 ∧ False)) ∧ p3)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h10 : (p2 → (False ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h12 := h7 h10
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h14 : (p2 → (False ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h15
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h16 := h7 h14
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308638318126691155614414236134 : (p2 ∨ ((True ∧ (True ∧ (((p2 → (((p1 ∨ p5) ∧ p1) ∧ False)) ∨ p1) ∨ ((p3 ∧ ((p3 → (p3 → False)) ∧ False)) ∧ (p4 ∨ p5))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196644941121752944130053073484 : ((((((True ∧ p2) ∧ p5) ∧ True) ∧ p3) ∧ False) ∨ ((p4 → ((True → p1) ∨ (p1 ∧ (True ∨ True)))) ∨ (((p4 → p1) → (p1 ∧ True)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140903458013855830563554696125 : ((((p4 → (p2 → ((p5 ∧ p2) ∧ (p2 ∧ p4)))) → False) ∧ (((p3 ∧ (p3 ∧ (p4 ∨ p2))) ∧ (p5 ∨ p4)) ∨ p3)) → ((p2 → False) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_376401521662902610844453053927 : ((((p1 ∨ (((False ∧ p2) ∨ (((True ∧ p2) ∨ p2) ∨ (True ∨ ((p4 ∨ p1) ∨ True)))) ∧ (False → (((True ∧ p4) ∨ False) → p2)))) ∧ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h1
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681673129428583605618122431138 : ((((p4 → (((((True → (p1 ∨ (p4 ∧ p1))) → (p5 → True)) → p5) → True) ∨ ((True ∨ True) ∨ True))) → ((True → p5) ∨ (True ∨ p2))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_64540256076561578605901964229 : ((p1 ∨ ((True → (((False ∨ p5) ∨ p5) → False)) ∧ (p2 ∨ ((p1 ∨ (p5 → (p5 ∨ (p4 → p5)))) → (p4 ∨ (False ∨ (True ∨ p1))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306190076672691523347526091849 : (p1 ∨ ((p2 ∨ (p5 ∨ p1)) ∨ ((True ∨ (p5 → p4)) ∧ ((p5 ∧ True) ∨ (p5 → ((((p5 ∨ p2) ∧ p2) ∨ (False → (True ∧ p3))) ∨ p2)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319553788546513523943889757126 : (p4 ∨ (((False → p3) → (((True ∨ p5) ∧ (True → True)) → p5)) ∨ ((True ∨ ((p1 → ((p3 → False) → (p5 → p3))) ∧ (p3 ∧ p5))) ∨ p2))) := by
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
theorem thm_5_vars_350071884374975166626859389563 : (p4 → (((False ∧ ((p1 → (True → p2)) ∧ ((p1 ∧ False) ∧ ((((p4 → p5) ∧ (p1 ∨ (p2 ∨ p4))) ∨ False) ∧ p3)))) ∨ (p1 → p1)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340863739347392209795661657840 : (p2 → ((((((p4 ∧ ((((p2 ∨ (p2 → p3)) ∨ (p1 ∨ p1)) ∨ p1) → False)) → False) ∨ True) → p3) ∨ (p2 ∨ ((p3 → p2) → p5))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115539845256780297069169470248 : (((p4 ∨ ((p3 ∧ (p4 ∨ True)) ∧ (p4 ∨ True))) → (((p2 → p3) ∧ False) ∨ ((((p2 → (p5 ∨ p3)) ∧ p4) ∧ False) ∧ p4))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148670152545474407074544349058 : ((((p5 ∧ (p3 ∧ ((p3 → True) ∧ True))) ∧ p3) ∨ (p3 → ((p4 ∨ ((True → p5) ∧ p2)) ∨ (True ∧ True)))) ∨ ((p4 → (p5 ∨ p2)) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_192270494773709385322145452738 : ((((p2 ∨ (p3 ∧ False)) → (p2 ∧ (p5 → True))) ∧ p5) → (p3 ∨ ((p1 ∧ (p3 ∧ p1)) → ((((False → p5) ∧ p5) → (p2 ∧ p3)) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682951769918781636505376834935 : (((((p4 ∨ p3) ∨ (((p4 ∧ p3) ∧ True) → ((True ∧ ((True ∨ True) → (p1 ∨ p2))) → True))) ∧ (p2 ∧ ((p4 ∧ (p2 ∧ True)) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171581243435101380481192365528 : ((((((p1 ∨ p4) → (p3 ∨ False)) ∨ ((False ∧ p4) ∨ p3)) → (p5 ∧ p4)) ∨ True) ∨ ((p5 ∨ p3) ∨ ((p3 ∧ p5) ∧ ((False ∨ p2) → p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53530447176805834307288936860 : (((p4 → (True → ((p2 → ((p4 ∧ p1) → (False ∧ p5))) → p4))) → (False ∨ (((((False → False) → p1) ∨ (False ∧ True)) ∧ True) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679045542318224390914000290930 : ((((False ∨ ((((p3 → True) ∧ p2) ∧ p4) ∧ (((p2 → (p3 ∨ p5)) ∨ False) → ((p2 ∨ False) ∧ p3)))) ∨ ((p1 ∨ True) → (p1 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192659391418772186656342643265 : (((((((p1 ∧ p5) → p4) ∨ False) → p2) → p3) → p3) → (p5 → (((True → p1) ∧ p2) → (((((p5 ∨ p1) → p2) → p1) ∨ p2) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616078605236948529220972200207 : (((((p1 → ((p1 → ((False ∨ (((p1 ∧ p3) ∨ p2) ∨ True)) → False)) ∨ False)) → (p1 ∨ (p4 ∧ (p2 ∨ (p4 ∨ (p4 ∧ p3)))))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148173491302348036233045774450 : (((((((True ∨ p4) ∧ (p3 ∨ ((p1 ∧ p3) ∧ (p3 → p4)))) ∧ p2) ∨ p2) → False) ∧ ((False ∧ p5) → True)) ∨ (p2 → (p2 ∨ (p2 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191942205300735485031419183830 : ((True → ((p3 → p3) → (((p2 ∧ p5) ∧ p3) ∨ False))) ∨ ((p2 ∧ p1) → (p4 ∨ (((((True ∨ p4) → (p4 ∧ False)) → p5) → p2) → True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147736335725348582085046921940 : ((((p2 ∧ (p4 ∨ (p2 ∧ p3))) ∧ ((((p1 ∧ ((True ∨ p2) → p3)) ∨ False) ∨ (p3 ∧ True)) → True)) → p3) ∨ ((p5 → (p4 → True)) ∨ p2)) := by
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
theorem thm_5_vars_152675919562846350218382671445 : (((p5 → p5) ∧ ((p5 → (p5 ∧ (((p2 → p1) ∨ p3) → (p3 ∧ p3)))) ∨ ((p1 ∧ (True ∨ p3)) ∨ p2))) → (p3 → (p1 ∨ (True → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
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
        -- Implications on the right can always be decomposed.
        intro h12
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709562922622737998515990753114 : ((((False ∨ (((p3 → p5) ∨ False) ∧ (p2 ∧ p4))) → (((p2 → ((((p3 ∨ p5) ∧ False) ∨ p3) ∧ False)) ∨ True) ∨ ((p3 ∧ False) → False))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57571589122331602807517456631 : ((((p1 ∨ p1) ∧ p1) → (((((p5 → p2) ∨ ((p4 ∨ (p1 ∨ p4)) ∨ p1)) → ((p2 → False) → p2)) ∨ False) ∧ (p5 → (False ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258702060343555287096109816148 : ((True → True) → ((((p3 ∧ (((p4 → (((p2 ∧ (p5 ∧ (True → p2))) ∧ p5) ∧ p1)) ∧ (p4 ∨ True)) ∨ (p2 ∨ p4))) ∧ p5) ∨ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58185846409954169411378141352 : (((p3 ∧ p4) ∧ (((False ∨ (((((p1 ∧ (p2 ∧ (True → p1))) ∨ (p1 ∧ p1)) ∨ (p4 → True)) ∨ (False → p3)) ∧ True)) ∨ p1) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_451802464708484187069673934872 : ((((((p1 → ((p3 ∧ p4) ∨ False)) → p4) ∧ ((((False ∨ (p4 ∨ p1)) ∧ False) ∧ p2) ∨ (p2 → p2))) ∨ (p4 → ((False → p1) ∨ p3))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317799960361782712002763997310 : (p4 ∨ ((((False ∨ p2) ∨ (((True ∧ p5) ∨ p1) ∨ True)) ∨ ((((False → (False ∨ (p1 ∨ (False → p4)))) → (p4 ∨ p4)) → p2) ∧ p2)) ∨ p5)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172285165623221211431535567724 : (((p4 ∨ ((p3 → (p3 ∨ (p5 ∨ p5))) → p4)) ∨ ((p5 → (True ∧ False)) ∧ p5)) ∨ ((((True ∧ ((p3 ∨ p1) → False)) ∧ p1) ∧ p1) → p2)) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : (p3 ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622621459859185652320247432780 : ((((p4 ∧ ((((((((p2 → (False → False)) ∨ False) → (p3 ∧ (p3 → p1))) → (p2 → p5)) ∧ p4) ∨ p1) ∧ p2) ∨ (p2 → p1))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_54312368043394040669480771660 : ((((True → False) → ((p4 → (p4 ∧ p5)) ∧ p5)) ∧ (((p2 ∨ (p2 ∧ True)) → (((p2 ∨ p2) ∧ p5) → (p2 ∧ False))) ∧ (p3 ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733468783284857075557141657659 : ((((p4 ∧ p2) ∧ ((((((p5 ∨ ((p2 ∨ True) ∨ p3)) ∨ (p5 → True)) ∨ p5) ∧ ((p5 ∨ (True ∨ (p5 ∨ True))) → p2)) → p3) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184682108484534308408599694688 : (((p5 ∨ (p5 ∨ ((p1 ∨ False) ∧ p2))) ∨ ((p2 → p4) ∨ p1)) ∨ (((p4 ∧ ((p3 ∧ p3) ∨ (p4 ∨ p1))) → p5) → (p5 ∨ (p3 ∨ True)))) := by
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
theorem thm_5_vars_731573152217169069835476890672 : ((((False → (p4 → p1)) → ((p1 → p5) ∨ (((p5 ∨ ((False ∧ p5) ∧ ((p2 ∨ p3) ∧ False))) ∨ p3) ∨ (True ∨ (False ∨ (False ∧ p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46074789802535027386421942450 : ((((((p3 ∨ (p3 → (((p5 ∨ (p4 ∧ (p4 → (p1 → (False ∨ p2))))) → False) → True))) → p2) ∨ (p3 ∧ p3)) ∨ p4) ∧ (False ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166173904545339775323550765685 : ((False ∧ (p2 ∨ (False ∧ (True → (True → ((((p2 ∨ p3) ∨ p4) ∨ (p2 ∨ p1)) → p1)))))) ∨ ((p5 → p2) → (False ∨ (p1 → (p5 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118743617984461681904478789963 : ((p5 ∨ ((False ∨ (p5 ∧ (False ∨ (p1 ∧ p2)))) ∨ (p5 → (p2 ∧ ((((p3 ∨ (p1 ∧ (p4 ∧ p3))) ∨ p2) → True) ∨ True))))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



