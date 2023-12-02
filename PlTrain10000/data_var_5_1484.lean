variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4319793923877487965164497907 : (True → (p5 → ((p4 ∧ (((p2 → (p2 ∧ (False ∨ p5))) ∨ p2) → (False ∧ p3))) ∨ ((((p4 → p3) ∧ p4) ∧ (False ∧ p5)) → True)))) := by
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
theorem thm_5_vars_315108819575037768950027266872 : (p3 ∨ (((p1 ∨ (p5 ∨ (p5 → p1))) ∧ p1) ∨ (((p2 ∨ p3) ∨ True) → (p4 → ((True → p4) ∧ (p4 ∨ ((p5 ∨ p4) ∨ (False → p4)))))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314243454135079318150955969870 : (p3 ∨ ((((((p2 → (p4 ∨ ((((p3 ∧ p5) → p1) → False) ∨ p4))) → (p1 → False)) ∧ p1) → False) → (p4 ∧ p3)) ∨ (True ∨ (p4 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670258198134828414838290561431 : ((((((False → (False → p2)) ∨ p5) → (((p3 ∨ (p2 ∨ False)) ∧ ((p4 ∧ True) ∨ p5)) ∨ (True → (p3 → p1)))) ∨ (p4 → (False → p3))) ∨ p5) ∧ True) := by
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
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174789313759899579512785126508 : (((p2 ∨ p2) ∧ (True ∧ ((p5 ∧ ((p4 → p2) → ((True → p2) ∨ p1))) → False))) → ((p2 → ((True → True) → p1)) ∨ ((True ∨ p5) → p2))) := by
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
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h3.left
    let h12 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149598051749789260767277649470 : ((p3 ∧ (((((p1 → p4) → (False ∧ p4)) ∨ p3) ∨ (p5 ∧ (p2 ∧ p1))) ∧ ((p5 ∨ (p1 ∨ p5)) → p4))) ∨ ((p1 ∨ (True ∨ True)) ∨ p4)) := by
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
theorem thm_5_vars_258479690345757480464911323074 : ((p5 ∨ p2) → (((p5 → ((p1 → (p4 ∧ p2)) ∧ ((((p1 ∧ True) → True) ∨ p2) ∧ p5))) ∧ p1) ∨ (((p4 ∧ p3) ∨ (p4 → p5)) ∨ True))) := by
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
theorem thm_5_vars_196944339211355451429707914095 : (((((p3 ∧ (False ∧ p3)) ∨ p2) ∨ p5) ∨ False) ∨ (((p4 ∧ (((((p4 ∨ (p5 → p1)) ∨ p3) → p1) → p4) ∨ (p4 ∧ p4))) → False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657307284019816116436924280722 : (((((p4 ∧ True) ∧ (p1 ∧ (True → (p4 ∧ (((False → (p5 ∨ p4)) → (p3 → (p5 ∨ (p2 → p4)))) ∨ (p3 ∧ p5)))))) ∨ (False ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124064762868936920771543281705 : ((((False → p2) ∨ (True ∧ (p1 ∨ (p4 → ((p2 ∨ p2) ∨ p1))))) → ((p1 ∧ ((p4 ∨ (p1 ∧ (p3 ∧ p2))) ∧ False)) ∧ p5)) → (False ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False → p2) ∨ (True ∧ (p1 ∨ (p4 → ((p2 ∨ p2) ∨ p1))))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : ((False → p2) ∨ (True ∧ (p1 ∨ (p4 → ((p2 ∨ p2) ∨ p1))))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h8
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321675565659775370548119803592 : (p4 ∨ (p4 → (((p2 → (((p3 ∨ ((p1 ∧ p3) ∨ False)) → p2) ∧ (p2 → False))) ∧ (p5 ∧ (p2 ∨ p2))) → (p3 ∨ (p3 ∧ (True ∧ p4)))))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h14 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h15 := h3 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h17 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h18 := h16 h17
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342803973429561325869303006154 : (p2 → ((p1 → ((p1 → p4) → ((p5 ∨ p4) ∨ p4))) → (p3 → (((p5 ∨ p2) ∧ (p2 ∨ ((p4 ∧ p4) → (p3 ∨ False)))) → (p4 → p4))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149620602416768657937787474947 : ((p3 ∧ (True → (((p3 ∧ ((p2 ∨ (p1 → ((p5 ∧ False) ∨ (False ∨ p3)))) ∧ (p2 ∧ p4))) ∨ True) ∧ p2))) ∨ ((p5 ∨ p2) → (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166280976106428266918442055976 : ((p4 ∧ (((p1 ∧ (False ∧ True)) ∨ ((p4 → (p1 → (p1 → True))) ∧ (p5 ∧ False))) ∨ p2)) ∨ ((((p1 → p3) ∨ (p3 ∨ p4)) → True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148747872755439059874820559251 : ((((p3 ∧ p1) ∨ ((p2 ∧ p5) → False)) ∧ (p5 ∧ ((p4 ∨ True) → (((p1 ∧ (True ∧ False)) ∧ True) ∨ True)))) ∨ ((False → p1) ∨ (p4 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142719972095942349658602069636 : ((p2 ∨ ((False → (((p5 → p4) → p4) → (False ∨ (((p2 ∧ p1) ∧ (p3 ∨ p3)) ∧ (True ∨ (p2 ∧ p3)))))) → False)) → ((False ∧ False) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (False → (((p5 → p4) → p4) → (False ∨ (((p2 ∧ p1) ∧ (p3 ∨ p3)) ∧ (True ∨ (p2 ∧ p3)))))) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h4
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68208637554288429074225202464 : ((p3 → ((p2 → (((p3 ∨ p3) → (False ∨ ((p2 ∨ p5) → ((((p5 ∧ p2) → p2) → (p5 → False)) → (p4 → False))))) ∨ p2)) ∨ p2)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299726398591826081066453990960 : (False ∨ ((((p3 ∧ (True ∨ p4)) ∨ (p2 → (True → (True → p2)))) → ((((p1 ∨ p5) → p2) ∧ (p4 ∧ (p3 ∧ (False ∨ False)))) ∧ True)) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∧ (True ∨ p4)) ∨ (p2 → (True → (True → p2)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_73754450779020546317282928664 : (((((True ∨ (p4 → p5)) → ((p5 → p2) ∧ (p4 ∨ ((p1 ∨ True) → False)))) ∧ (p3 → (p3 ∧ ((p2 ∧ True) ∧ (False ∨ p2))))) ∨ p4) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (True ∨ (p4 → p5)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : (p1 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h11 := h9 h10
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302029109909950656155165420924 : (False ∨ (True ∧ ((p2 ∧ ((p5 ∧ (((p3 ∨ p3) → (p2 ∧ p1)) ∧ ((p4 → p4) ∨ False))) → (p5 ∧ p1))) ∨ ((p5 → (p5 → True)) ∨ p4)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172089920721498757886233926209 : ((((p5 → p4) ∨ ((p2 ∧ (p3 ∧ (p1 → (p4 → p2)))) ∧ True)) → (True ∧ p5)) ∨ ((((p3 ∧ p4) ∧ p5) ∧ p1) → (p3 ∧ (p2 ∨ True)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56157348165932096798756914047 : (((True ∧ (p2 ∧ (p5 → p2))) ∨ (((((((p2 ∧ (True → p4)) ∨ (p5 ∨ True)) → p4) → ((p3 ∨ p1) ∨ p4)) → False) ∨ p4) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174798378606456652487352305708 : (((p5 ∨ p2) ∧ (p2 ∨ (((True ∨ True) → (p5 ∨ False)) ∧ ((p3 → p5) → p3)))) → (((p4 → p5) → (p4 ∨ (p5 ∨ True))) ∨ (False ∧ True))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h17
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54742138688811935299362379179 : ((((p2 → (p3 → False)) → (p5 ∧ (False ∧ p5))) → (((((False → (((p5 ∨ True) ∧ False) ∧ p1)) → p5) ∨ p2) ∧ (p1 ∧ p1)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684841525686452553248529734657 : (((((False → False) → (((p4 ∨ p5) ∨ ((False ∧ p1) ∨ p4)) ∨ ((False ∧ (p3 ∨ p2)) ∧ p2))) ∨ (((p5 ∧ (True → p2)) ∧ False) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318618347836587586224495923044 : (p4 ∨ (((True ∨ False) ∧ ((p3 ∨ ((p2 ∨ (p4 ∨ (p5 → ((True → False) ∨ (p4 ∨ True))))) ∧ (False ∧ p5))) ∧ (p4 ∨ p2))) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_860180411632050420758128685403 : ((((((p1 ∨ p1) → ((p4 ∨ (p4 → ((True → (False → False)) ∨ p2))) → (False ∨ (p3 → (p3 → (p4 ∧ p3)))))) ∨ (p5 → True)) → p5) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ p1) → ((p4 ∨ (p4 → ((True → (False → False)) ∨ p2))) → (False ∨ (p3 → (p3 → (p4 ∧ p3)))))) ∨ (p5 → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184522571693139879284844361823 : (((p4 ∨ ((p4 ∨ (p3 → True)) → (False ∧ p5))) ∨ (p1 ∧ p4)) ∨ (((((p5 ∧ p2) ∧ (p5 → (p2 ∨ False))) ∧ False) ∧ (p4 ∨ p3)) → p2)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231888565151666417947834293839 : (((True ∨ p4) → False) → (False ∨ (((((True ∨ p3) → p2) → (False → p4)) → p3) ∨ ((p2 ∧ ((p4 ∧ True) ∧ (p4 ∧ p4))) ∧ (p1 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231730754204622270293332454518 : (((p2 ∧ p4) → False) → ((((p3 ∧ (p3 ∨ (True ∧ (p4 ∨ (False → False))))) ∧ p3) ∨ (False ∨ (p2 ∨ (False → True)))) ∨ (p1 ∧ (True → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612622449019344180150499155663 : ((((((p2 → ((((p5 → p1) ∨ False) ∨ p3) ∨ (((((False → p1) ∧ True) ∨ p1) ∨ p5) → p3))) ∨ (p4 ∨ True)) ∨ (True → p4)) ∨ p1) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141129025885925491421809991278 : (((((p1 ∨ (p1 → p2)) ∨ p2) ∧ p4) ∧ ((((((True → p1) ∨ p1) → p4) ∨ (p1 ∧ p2)) ∨ (p1 ∧ p4)) ∧ p4)) → (True → (p2 ∨ p4))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h9 := h4.left
      let h10 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h4.left
      let h21 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h24.left
          let h26 := h24.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h21
      case inr h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21
  case inr h30 =>
    -- Conjunctions on the left can always be decomposed.
    let h31 := h4.left
    let h32 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h31
    case inl h33 =>
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h34 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h32
      case inr h35 =>
        -- Conjunctions on the left can always be decomposed.
        let h36 := h35.left
        let h37 := h35.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h32
    case inr h38 =>
      -- Conjunctions on the left can always be decomposed.
      let h39 := h38.left
      let h40 := h38.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173890618591126535160960243093 : ((((False ∧ (((p1 ∧ p1) → p2) ∧ (False ∧ ((False ∧ p3) ∧ p5)))) ∨ p4) → p5) → ((p4 ∧ False) ∨ (p5 → (((p4 ∨ p4) ∧ p2) ∨ p5)))) := by
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
theorem thm_5_vars_41063849035054816056991001034 : ((((p4 ∧ ((p3 → p4) → ((p3 ∧ ((((((p4 ∧ p5) ∨ (p2 ∨ p2)) ∧ p3) ∧ p3) → True) ∨ True)) ∨ p5))) → (p2 ∧ p4)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806184523024795451737039422156 : (((p4 → (((p5 ∧ ((((((((p2 ∨ p3) → p4) → p3) ∨ p3) → (p1 → True)) ∨ (True ∧ (p3 ∧ p1))) → False) ∧ False)) ∨ False) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251704298958132379502633686931 : ((p3 → p2) ∨ (p3 ∨ ((p1 ∨ (((((p4 ∧ p5) ∨ (p5 → p1)) ∨ p2) ∧ (p1 ∧ True)) → p1)) → ((p4 ∧ (True → (p1 ∧ p1))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_769902689156493903185776266281 : (((p5 ∧ (True → ((True → (p1 ∧ p5)) ∨ (((p3 ∧ p1) ∨ (((((p5 ∧ ((p5 → p2) ∨ False)) ∧ p1) → p3) ∧ p1) ∨ p1)) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177767201485116756640363233987 : (((True ∧ (((False → p5) → ((p1 ∧ False) ∨ (p4 → p3))) → p1)) ∧ p4) ∨ (((True ∨ ((p3 → True) ∧ True)) → ((False ∧ p3) ∨ p2)) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ ((p3 → True) ∧ True)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218676966895341862693624259693 : ((True ∧ (p5 ∨ (True → True))) → (((False ∨ False) ∧ (p3 ∧ (False ∧ (p1 ∧ p4)))) ∨ ((False ∧ ((p5 ∧ False) ∧ (p5 ∧ (p1 ∨ p3)))) → p5))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735304350893697900852108944652 : ((((p4 ∨ True) ∧ (p1 ∨ ((((((p4 → p4) → False) ∨ (p1 → True)) ∨ ((((False ∨ p1) ∧ p1) ∧ (False ∨ p5)) → True)) ∨ p1) ∨ p4))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_702953557882375079715995712551 : ((((((p2 → p4) ∨ False) ∨ (((p4 ∨ p3) → p2) ∧ p5)) ∨ (p5 → (p2 → ((p5 ∧ (p2 ∧ ((p2 ∨ (p2 ∨ False)) ∨ p1))) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164509059150622292154629736843 : (((((((p4 ∧ p5) → (True ∧ p3)) ∧ (p2 ∨ (p3 ∧ p5))) → p1) ∧ (p1 ∨ p2)) ∧ p5) ∨ (((p1 ∧ p1) → (p2 → False)) → (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39614558600811324215284351831 : (((p2 ∨ ((p4 ∨ p5) ∧ ((((True ∧ ((True ∧ p1) ∧ p1)) ∨ p3) ∧ (p3 → ((p2 → (False ∨ (True ∧ p4))) ∨ True))) ∨ False))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704907634576754752223401344380 : ((((p3 ∨ (True → (p2 ∨ (p2 ∨ ((True ∧ p4) → p5))))) → (((p4 → p3) ∨ ((p5 → ((p5 → (p5 ∨ True)) ∨ p1)) ∨ p5)) ∨ p4)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118395729032820785393159910760 : ((p2 ∨ ((True ∨ (p2 → False)) ∧ ((p4 ∨ ((False ∨ (p2 ∧ p5)) ∨ (p4 ∧ (p3 → p2)))) ∨ (False → (p1 → (p4 ∧ p2)))))) ∨ (p4 ∧ False)) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646264541661469930600616521005 : ((((False → ((((p4 → p5) ∧ (p1 ∧ True)) → (True ∧ p1)) ∧ (False → (((p1 → p5) ∨ p1) ∨ ((p5 ∧ (p1 ∧ p4)) ∧ p4))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43660868525337577551687190464 : ((((((p4 ∨ ((True ∨ ((True → (p5 → (p3 ∨ False))) → True)) ∨ p1)) ∧ (False ∧ p1)) ∧ ((p1 → False) ∨ (True ∨ p5))) → p1) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38681901939165255792453357884 : ((((p3 ∧ (True ∨ (p5 ∨ (True → False)))) ∧ ((True → ((False ∧ False) ∨ ((((p2 → True) ∧ True) ∨ p1) ∧ (p5 → True)))) → p4)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68759111528817406195819334217 : ((p4 → (((((p5 → p2) ∨ p2) ∨ p3) → (p1 → ((p1 → True) → (p4 ∧ p2)))) → ((p3 ∨ p3) ∧ ((p1 → False) ∨ (p4 ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_855680243852243902807287303773 : ((((((((p5 ∧ ((p2 → p5) ∧ p4)) ∧ p3) ∨ (p3 ∨ ((p3 ∨ p1) → (p3 ∧ ((False ∨ (p1 ∧ True)) → p3))))) ∨ p4) ∨ True) → False) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p5 ∧ ((p2 → p5) ∧ p4)) ∧ p3) ∨ (p3 ∨ ((p3 ∨ p1) → (p3 ∧ ((False ∨ (p1 ∧ True)) → p3))))) ∨ p4) ∨ True) := by
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
theorem thm_5_vars_115250360256327473810527650679 : ((((p5 ∧ ((p5 ∧ p2) ∨ False)) ∧ ((p2 ∨ p2) ∧ True)) ∨ ((p5 ∨ (p3 → False)) ∧ (p2 → (p2 → (p2 → (True ∨ p4)))))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747463874338130156640817146679 : ((((True → False) → (p1 ∧ (p2 ∨ (((p2 ∧ (True ∧ p1)) ∧ (p2 ∧ ((p1 ∧ ((p5 ∧ ((False → True) → p5)) ∨ p5)) ∧ False))) ∧ p3)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246116419273779705577815905315 : ((p4 ∧ p1) ∨ (p2 ∨ (((p5 ∨ (True ∧ ((p1 ∨ p3) → False))) → p5) → (p2 ∨ (p2 ∨ ((p1 ∨ (True → (False → False))) ∨ (p2 → p4))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243297402315559089075829752991 : ((p4 → p4) ∧ ((((p1 → (p4 ∨ ((p3 ∧ (p3 ∧ True)) ∨ (False ∨ True)))) ∧ True) → (p4 ∨ p2)) ∨ ((True ∧ False) → (p1 ∧ (p1 ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759576808017471768191506825060 : (((p2 ∧ ((p1 ∧ ((False ∧ (p3 ∧ ((((False ∨ p4) ∧ p2) ∨ p3) → (p3 → p3)))) ∨ p5)) ∨ (p1 ∨ ((True ∧ (p2 ∨ False)) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182618084586934061859819769682 : ((((p4 ∧ p5) ∧ ((p5 ∧ p4) ∧ p3)) ∨ (p2 → (p2 → True))) ∧ ((p4 → ((False ∧ (True → p2)) ∧ (p3 → p3))) → (False → (p4 ∨ False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687927672195532463107509187791 : (((((False ∧ ((((p3 ∧ p2) ∨ p3) ∨ p1) → p1)) ∧ (p1 ∨ (p1 → (True ∧ p5)))) ∧ (((p3 ∧ (p4 ∨ p2)) → p2) ∧ (p4 ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323673437385629946731634510069 : (p5 ∨ ((((p2 ∧ p4) → p3) ∧ ((p1 ∧ (((p2 → p1) ∧ (p2 ∨ True)) ∨ True)) ∨ ((p1 ∨ False) ∧ p4))) ∨ ((p4 ∧ False) → (True → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777535908013536537431558350001 : (((p1 ∨ (((p1 ∧ ((((p3 → (False ∧ True)) ∨ p4) → p5) ∧ p4)) → p5) ∧ ((((False ∨ p4) ∨ (p3 → p2)) ∧ p1) ∨ (p2 → True)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((p3 → (False ∧ True)) ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174674752498560777402779754337 : (((False → (p1 ∧ p3)) ∧ (((False ∧ (p3 → ((p4 ∧ p3) ∧ p1))) ∧ True) → p2)) → (p1 ∨ ((p2 → (p2 ∨ (False ∨ (False → p2)))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50098270018221760702112260508 : (((p4 ∧ ((p2 ∧ ((((p5 ∧ True) ∨ ((True → (True → False)) ∨ (p3 ∧ True))) → p5) → False)) ∨ p4)) ∧ (p2 → (p4 ∨ (True ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133755096792424857385187176583 : ((((((p1 ∧ True) → (p4 ∨ False)) → p4) ∧ (((False ∨ p3) → (p1 → p5)) ∨ ((p3 ∧ (p2 → False)) ∧ p1))) ∧ p5) ∨ ((p4 ∧ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44837919367054830107175482944 : (((((True ∨ p5) ∨ True) ∨ (p1 ∧ ((p2 ∨ False) ∨ (p2 → (p2 ∧ ((((((True ∧ False) ∧ p2) ∨ p4) → p3) ∧ p2) ∧ True)))))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232028636143844503646945981741 : (((p3 ∨ p1) → False) → (((p4 ∧ ((((p4 ∧ (p4 → (False ∧ (p4 → False)))) ∧ (True ∨ ((True ∨ p2) ∨ True))) → p1) → p3)) ∨ p1) → False)) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (((p4 ∧ (p4 → (False ∧ (p4 → False)))) ∧ (True ∨ ((True ∨ p2) ∨ True))) → p1) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h12 =>
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h13 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h14 := h11 h13
        -- We need to get the left conjuct of h14 based on <expert-advice>.
        let h15 := h14.left
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
            -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
            have h19 : p4 := by
              -- One of the premise coincides with the conclusion.
              exact h10
            -- We have shown the premise of h11, we can now drive its conclusion.
            let h20 := h11 h19
            -- We need to get the left conjuct of h20 based on <expert-advice>.
            let h21 := h20.left
            -- False on the left can always be used.
            apply False.elim h21
          case inr h22 =>
            -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
            have h23 : p4 := by
              -- One of the premise coincides with the conclusion.
              exact h10
            -- We have shown the premise of h11, we can now drive its conclusion.
            let h24 := h11 h23
            -- We need to get the left conjuct of h24 based on <expert-advice>.
            let h25 := h24.left
            -- False on the left can always be used.
            apply False.elim h25
        case inr h26 =>
          -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
          have h27 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h10
          -- We have shown the premise of h11, we can now drive its conclusion.
          let h28 := h11 h27
          -- We need to get the left conjuct of h28 based on <expert-advice>.
          let h29 := h28.left
          -- False on the left can always be used.
          apply False.elim h29
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h30 := h5 h6
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h31 : (p3 ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h30
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h32 := h1 h31
    -- False on the left can always be used.
    apply False.elim h32
  case inr h33 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h34 : (p3 ∨ p1) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h33
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h35 := h1 h34
    -- False on the left can always be used.
    apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326966321705247969211845955069 : (True → ((((False ∨ (p5 → p1)) ∨ ((True ∧ ((p4 ∨ ((p2 ∧ p4) → (p2 ∧ True))) ∧ p3)) ∧ ((p3 ∧ False) → p5))) → (p1 → p1)) ∨ p2)) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141867680060963718801205222890 : (((True → False) ∨ (p1 ∨ ((p1 → p4) → (p4 ∨ (p3 → (((p3 ∧ p3) ∧ (p5 ∧ (p3 → (p3 → p3)))) ∧ p2)))))) → (p2 → (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_821219684183458757962448595296 : (((((((False ∨ p4) ∧ (((p3 → (False ∧ True)) ∨ p1) ∧ p4)) → ((p3 → p1) → p5)) → ((((p3 ∨ p5) ∧ p4) ∧ p4) ∧ p4)) ∧ p5) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((False ∨ p4) ∧ (((p3 → (False ∧ True)) ∨ p1) ∧ p4)) → ((p3 → p1) → p5)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h8.left
      let h12 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h15 := h2 h4
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- One of the premise coincides with the conclusion.
  exact h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254030653806845027864338469242 : ((p2 ∧ True) → ((p2 → (((p2 ∧ False) → ((((False ∨ p4) ∨ (p5 → p1)) → (p2 ∧ (p5 ∨ (p1 ∨ (p4 ∨ p5))))) → p1)) → False)) ∨ p2)) := by
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
theorem thm_5_vars_751256428937114804607710619127 : (((True ∧ ((p3 ∧ False) ∧ ((p1 → ((p2 → (p2 ∧ False)) → ((((p3 ∨ p5) → p4) ∧ (p1 ∨ (p2 → p2))) ∨ (p5 ∨ True)))) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234790691886123768321335817420 : ((p5 → (p2 ∧ p1)) → ((((p3 ∨ True) ∨ True) → p3) ∨ ((p3 ∧ ((p3 ∨ p4) ∨ ((True ∧ p4) → (p1 → False)))) → (False → (p5 ∧ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53084458318061944921405911527 : (((True ∨ (p3 ∧ (p1 ∨ ((p1 ∧ ((p1 → p2) ∧ False)) ∨ p2)))) ∧ (((p1 ∧ False) ∧ (False ∧ (p1 ∨ ((False ∨ p3) ∧ p3)))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342397318282114261850849937666 : (p2 → (((p2 ∧ p4) ∨ ((p1 → ((True ∧ p5) ∨ (p5 ∨ (False → (p2 → False))))) ∧ p1)) ∨ ((((p5 ∧ p1) ∨ p2) ∧ (p5 → True)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340728835217767886997642486084 : (p2 → ((((((False ∨ p4) → (p5 ∧ (((((p4 ∨ p1) → p5) ∨ (p4 ∨ p5)) ∨ False) ∧ ((p3 → p5) → p4)))) → False) ∧ False) ∨ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151793703393054562969185088606 : (((p2 → ((((p1 → p3) ∨ False) ∨ True) → (True → (p1 ∧ (p3 ∨ (p3 ∨ True)))))) → ((p1 ∧ False) → p1)) → (((p2 → p3) ∧ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206862086343389803354335147763 : (((((p2 → p2) ∨ p5) ∧ p1) ∧ p2) → ((((False → p3) → (((p4 ∧ p4) ∨ (p4 ∨ p2)) ∨ p1)) ∧ (p5 → p1)) ∧ (p2 ∧ (False → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h14 =>
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h15 =>
    -- One of the premise coincides with the conclusion.
    exact h13
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h20 =>
    -- One of the premise coincides with the conclusion.
    exact h17
  case inr h21 =>
    -- One of the premise coincides with the conclusion.
    exact h17
  -- Implications on the right can always be decomposed.
  intro h22
  -- False on the left can always be used.
  apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230218883758124517346009720073 : (((True ∨ p1) ∧ p1) → (((((True ∨ (p1 → p3)) → (p2 → p4)) ∧ (True ∨ (p5 ∨ (p3 ∧ (p3 → (p5 ∨ True)))))) → p4) ∨ (p4 → True))) := by
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
theorem thm_5_vars_117592149483302506870910343782 : ((p2 ∧ (p5 ∧ ((False ∧ (p3 ∨ ((False → (p2 ∨ (p4 ∧ (((p4 ∨ p4) → (p3 → (p3 ∨ p3))) → p1)))) ∧ p5))) ∧ p5))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_35834826883635346902739217982 : ((p3 → ((((True ∨ p4) → True) → (p4 ∧ (((p4 → p5) ∨ p1) ∧ ((p4 ∨ (False → p4)) → (p2 ∧ (p5 ∨ (p4 ∧ p1))))))) ∨ p3)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346316437865109881955943676467 : (p3 → ((((((p1 ∧ (True ∧ p5)) → (p5 → ((p3 ∨ (((p5 → p4) ∧ p1) → p5)) ∨ p2))) → p5) ∨ p3) ∨ (p3 → p2)) ∨ (p3 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_34209596312613850905001414126 : ((True → ((p1 → (((((True → (True ∧ p3)) ∧ p2) ∨ (((p2 ∨ True) ∨ p3) ∧ (p4 ∨ p1))) ∧ False) ∧ (p4 ∧ False))) ∨ (True ∧ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345566087548488428950130319636 : (p3 → (((p3 ∨ (p2 → (p1 → p1))) → ((p2 ∨ p2) ∧ (((((p5 ∨ p1) ∨ True) ∧ p5) ∧ p2) ∧ ((False → p5) ∨ (False ∨ True))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341397476296808808261047971649 : (p2 → (((p3 → p4) ∧ ((p3 ∨ p5) ∧ (((p1 ∨ True) → p4) ∧ (p5 → (((p4 ∨ (p1 ∨ (p3 → p5))) → (p1 ∨ p1)) → True))))) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    let h8 := h6.left
    let h9 := h6.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h6.left
    let h14 := h6.right
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h15 : (p1 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h16 := h13 h15
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303803911579731296654464108313 : (p1 ∨ ((((p5 ∧ (p3 → (p2 ∧ ((p3 ∨ True) ∧ False)))) → ((((p1 → (p5 ∨ p1)) ∧ (p2 ∨ p1)) ∧ (p4 ∧ True)) → p1)) → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191324291654276665043091683093 : (((p1 ∧ p3) ∨ ((p2 ∧ (p5 → p3)) ∧ (p4 ∧ p2))) ∨ (((p3 ∨ (p1 ∧ (((True ∧ False) → (p4 → (True → True))) ∨ p4))) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655115811962659590242929779298 : (((((p3 ∨ (p4 ∨ ((True ∨ ((p2 → p4) → (p3 ∨ ((p5 → (((p2 ∨ p3) ∨ p2) ∧ False)) ∧ p5)))) ∧ p1))) → p2) ∨ (True ∨ False)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_264444742851878275806180993169 : (True ∧ (((p4 → p5) ∨ (p1 ∧ p5)) → ((((p5 ∧ (p5 ∧ True)) → (p5 → (p4 ∧ (False ∧ p4)))) ∨ (True ∨ p3)) → (False ∨ (False → True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h24
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194062181089894722039914275333 : ((p5 ∨ (p4 → ((p2 ∨ (False ∧ True)) ∨ (p4 ∨ True)))) → (((True → (((p4 → p4) ∧ (p2 → p5)) ∧ p4)) ∧ (True → False)) → (False ∧ p4))) := by
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
  cases h1
  case inl h5 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h9
    -- False on the left can always be used.
    apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h2.left
  let h12 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h13 =>
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h15 := h12 h14
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h17 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h18 := h12 h17
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615349627987146047189952440949 : ((((((p2 ∧ ((p2 ∧ True) → ((p4 ∧ False) ∨ p3))) ∨ (((p4 → False) ∧ True) ∨ True)) ∨ (p1 ∧ (True ∧ ((p3 ∧ p1) ∨ True)))) ∨ False) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66497567815948711496284466880 : ((True → (((False ∨ p5) ∨ (p3 ∨ (p4 ∧ (((p1 ∨ p3) → (((p4 ∧ True) ∨ ((False ∨ p2) → p4)) ∨ False)) ∨ (True → True))))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40154054283880936908247805591 : (((((((True → (p1 ∨ ((False ∨ p5) ∧ (p4 → p3)))) → p3) ∧ p2) → (((((True ∧ p3) ∨ p1) ∧ False) ∨ p3) → p4)) ∧ p4) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347832937073384353095789584592 : (p3 → (((False → p1) ∨ p5) → (p5 → (p1 ∨ ((p1 → ((p2 ∧ (p5 ∨ False)) ∧ True)) ∨ (False → (((p3 → p2) → True) → (p4 ∨ p4)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113699042294835445884029257405 : ((((p3 ∧ (((((p3 ∨ (p4 ∨ False)) ∨ p5) ∨ False) → False) ∧ ((p5 ∨ p4) ∧ ((p3 → p3) → p2)))) → False) → (p2 ∨ p4)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643140337647728390821981695268 : ((((p3 ∧ ((p4 ∨ (p2 ∨ ((p2 ∨ (p1 ∨ (False → p5))) ∧ (((p3 ∧ ((p1 ∧ p4) ∧ (p2 ∧ p1))) ∧ p2) ∨ p4)))) ∨ p1)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358004064137023955007991791969 : (p5 → (False ∨ ((p5 ∧ (True ∧ False)) ∨ ((((False ∧ p4) ∨ (p4 ∨ ((((p3 ∧ (p5 ∧ p3)) ∧ (True ∨ p4)) ∧ True) → p1))) → p2) ∨ True)))) := by
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
theorem thm_5_vars_308599299788165253305069113267 : (p2 ∨ (((False ∨ (False ∨ p3)) → (((False → False) → ((((p2 → (p5 → p2)) → p1) ∨ ((False ∨ (p5 → p3)) ∨ p4)) ∨ False)) ∨ False)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810312679271090176838829206195 : (((p5 → (((((((p2 ∧ p2) ∧ False) ∧ False) ∨ False) → p4) ∨ (p1 ∧ False)) → ((((p1 ∨ p2) ∨ (True ∨ p2)) → False) → (p4 → p3)))) ∨ p4) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : ((p1 ∨ p2) ∨ (True ∨ p2)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119318838117803968092253165138 : ((p3 → ((p1 ∧ ((p2 ∨ (((((p2 ∧ p1) → False) ∨ True) → p5) → (p1 ∨ p1))) ∨ p2)) ∨ (p2 ∨ (p1 → (True → True))))) ∨ (p3 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654371698169951304829851190367 : ((((((p1 → (((True → (p3 ∧ p2)) ∨ p2) ∧ (p4 ∧ False))) → (((p2 ∧ p4) ∨ ((p1 ∧ p3) → p3)) → p3)) ∨ False) ∨ (p5 → True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_62720166879721395317846715639 : ((p4 ∧ ((True → ((((((True ∨ False) ∧ False) ∧ (p5 ∧ ((True ∧ p2) → p4))) → p2) ∧ p3) → ((False ∨ p1) → (p2 ∨ p3)))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810618280883762238476756950398 : (((p5 → ((p1 ∨ ((p2 ∧ True) ∧ p2)) → ((p5 ∧ ((p4 → (p4 ∧ True)) → p1)) → ((p1 → ((p2 ∨ p2) → (True ∧ p4))) ∨ True)))) ∨ p5) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



