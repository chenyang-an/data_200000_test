variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653019760417082496134828157250 : ((((p5 ∨ (p3 → (True → ((False → p2) → (p1 ∧ (((p5 → p4) ∨ ((p4 → True) ∧ p2)) ∧ (p5 → (p1 ∧ False)))))))) ∧ (p5 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206877292498175554229265865793 : ((((p5 ∧ (p2 ∨ p2)) ∧ p1) ∧ p1) → ((p1 → (((p4 → (p5 ∧ p3)) ∨ (True → (False ∧ (p3 ∧ p4)))) → (p3 ∨ (False ∧ False)))) ∨ p1)) := by
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
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345401988000420531518966206992 : (p3 → (((((True ∧ p1) ∧ ((p2 ∧ ((p4 ∨ p5) → p3)) → (False → (((p5 ∧ (p4 → p3)) ∧ p3) ∨ p1)))) ∧ (p2 → p1)) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150668569300922534168061263159 : (((True → ((((((p3 ∨ p4) → (p3 ∨ ((p2 ∨ p1) ∧ p5))) ∨ p4) ∧ (p5 ∨ p5)) → p2) ∧ p1)) ∧ p4) → ((p2 ∨ p1) ∧ (p1 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251295339822194163555038634298 : ((p2 → p3) ∨ (((True ∧ (False ∨ ((((p5 → p5) ∨ p3) → p2) → False))) → (False ∨ (p1 ∨ (((p4 ∧ p1) → False) → (p3 ∨ p3))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328717062739981351900102632688 : (True → ((p5 ∨ ((((((p2 ∨ p4) → False) ∨ p5) ∨ p4) ∨ p5) ∨ p4)) ∨ (((((p5 → (p4 ∧ False)) ∧ p1) ∧ p3) ∧ (p1 ∨ False)) → p1))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160719732370741423527299299505 : (((p5 ∧ (False ∧ (p3 ∧ ((True ∧ p1) ∧ p5)))) ∨ ((p2 ∧ p1) ∨ (((p4 → True) ∨ p5) ∧ True))) → ((p3 ∨ (p4 ∧ False)) ∨ (p3 → p3))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- One of the premise coincides with the conclusion.
        exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741604722149217060479848697572 : ((((p5 ∨ p5) ∨ (p5 ∨ (False ∨ ((((p5 ∨ (p1 ∧ p4)) ∧ True) ∨ ((p2 ∨ p1) ∨ (((p4 → p4) ∨ p3) ∨ p5))) ∨ (True → p5))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192097080727197073079990540543 : ((p4 → (((p3 → p4) ∨ (p2 ∨ False)) → (True ∧ False))) ∨ (p5 ∨ (False ∨ (True ∨ (True → ((p4 ∨ False) ∨ ((p1 → (True ∨ False)) ∨ p4))))))) := by
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
theorem thm_5_vars_65682977950971666716911154458 : ((p4 ∨ (((False → (False ∧ (p3 → p2))) ∨ ((((p1 → ((False ∧ p3) ∧ False)) ∧ p4) ∧ False) ∧ (True ∨ ((p2 ∧ True) → p1)))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166305470072381781849799616766 : ((p4 ∧ (True → ((((p1 ∧ p2) ∧ p3) ∨ p5) → ((p1 ∨ False) ∨ ((p5 → p4) → p4))))) ∨ ((p4 → False) ∨ (True ∨ (p5 → (p2 → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634462337751639038175245836852 : ((((((p3 ∧ ((p4 ∧ (p1 ∨ (p2 ∧ p1))) ∨ (((p1 → p4) ∨ p1) ∧ (False ∧ False)))) → (False ∧ False)) ∧ ((p4 ∧ p5) → p4)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311930363302775564286538200069 : (p2 ∨ (p3 ∨ ((((((((p1 → p3) ∨ p2) ∧ ((p3 ∨ p4) ∧ (p5 → p5))) ∨ True) ∨ p2) ∧ (((p5 ∨ True) → False) → True)) → p5) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((((p1 → p3) ∨ p2) ∧ ((p3 ∨ p4) ∧ (p5 → p5))) ∨ True) ∨ p2) ∧ (((p5 ∨ True) → False) → True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264597117110148827759384189462 : (True ∧ ((p4 → (p2 → p1)) ∨ ((False ∨ (p3 → ((((p1 → ((False ∨ ((p5 ∨ p3) ∨ True)) ∧ p5)) → False) ∨ True) → (False ∧ True)))) ∨ True))) := by
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
theorem thm_5_vars_244369358725522937519154916785 : ((False ∧ p1) ∨ ((((((((False ∨ p3) ∨ p3) ∨ (False → False)) → (((p5 → p5) ∨ p3) ∧ (False ∧ p4))) → (p5 → p2)) ∨ p3) ∧ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((False ∨ p3) ∨ p3) ∨ (False → False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658684965816279691086939109927 : ((((p4 ∨ (((p3 ∧ (False ∨ True)) ∨ ((p5 ∧ ((True ∨ (p3 ∨ p3)) → (p5 ∨ p5))) ∨ p1)) → (p4 ∨ (p2 → p3)))) ∨ (False ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_179798823346940351031449740153 : ((((True → p5) ∧ ((True ∧ p5) → ((False ∨ (False ∨ False)) → p1))) ∧ p1) → ((False ∨ p3) ∨ (((False ∨ p5) → p2) ∨ (True ∧ (p4 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48664939158410192149344625739 : ((((((p4 → p5) → (((p4 → p4) ∨ p2) ∧ p4)) → (False ∨ False)) ∨ ((True ∧ (p3 → True)) ∨ (p5 ∨ p1))) ∧ (p3 → (False → p3))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192890766709679205697105472701 : (((p1 ∨ (p5 ∧ ((p2 ∨ False) → p5))) ∧ (p5 → True)) → (p3 → (((((p1 ∨ (p4 ∨ False)) ∨ p4) ∧ (p3 → (p1 ∨ True))) ∧ p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148429414401410767611514665295 : ((((p3 → p1) ∧ (True ∧ (p4 ∧ (((True → (True → p1)) → p5) ∨ False)))) → (p4 ∧ ((True → p3) → p3))) ∨ (p5 ∧ ((False ∧ p3) ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h12.left
  let h14 := h12.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h14.left
  let h16 := h14.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h17 =>
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h18 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h19 := h10 h18
    -- One of the premise coincides with the conclusion.
    exact h19
  case inr h20 =>
    -- False on the left can always be used.
    apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200827894149210002520190823387 : ((p5 ∧ (False → (p3 → ((p1 → p3) ∨ p2)))) → (((p3 ∧ (p2 → (p3 ∨ p3))) ∨ (p4 ∨ (p4 ∨ p3))) ∨ ((p3 → p2) ∨ (p2 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354641719739392464631345620947 : (p5 → ((((((((p1 ∧ (((True ∧ False) ∨ p3) ∨ p3)) → p2) → p3) → p1) ∧ (False ∨ ((False ∨ p3) → (p4 ∨ p3)))) ∨ False) → p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56501127585823494688861034694 : (((p2 ∧ ((True → p1) ∨ p4)) → ((((((p1 → p5) → p3) ∨ (p2 ∨ p4)) → ((p5 ∧ p5) → ((True ∧ False) → True))) → False) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233680798896736695133147423340 : ((p2 ∨ (False → p5)) → (True → ((p5 ∨ (False ∧ p1)) ∨ ((p2 ∧ p5) ∨ ((p2 ∨ p4) ∨ ((True ∨ ((p4 → (p1 ∨ True)) → True)) ∨ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57968472525224252632042931655 : (((p3 → (p1 ∧ p2)) → (True → ((p2 ∨ p2) ∧ ((True → p1) ∧ (((p1 → ((True → p2) ∨ False)) → (p1 → p3)) ∨ (p3 ∨ True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343671500354838850665562864226 : (p2 → (True ∧ (p5 → ((((p3 ∧ (p5 → (p1 ∨ p2))) ∧ False) ∨ p1) ∨ (p4 → ((False ∨ ((p1 → ((True ∨ p4) → False)) → p5)) ∧ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58938653501076327044579419985 : (((p1 ∧ p4) ∨ (p4 ∨ (p5 → (((((p3 ∧ (((p4 ∧ p4) ∨ p1) ∨ p2)) → (p1 ∧ True)) ∨ ((False → False) ∨ True)) → p4) ∨ p5)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65622755013139099513450248940 : ((p4 ∨ ((((p2 ∧ ((True ∧ True) → p2)) ∨ ((((p2 ∨ p5) → p1) → True) → (True → ((p1 ∧ p1) → (p4 ∧ p4))))) ∧ p5) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253134904658134058420369779051 : ((True ∧ p5) → ((p5 → ((p1 ∨ ((p4 ∨ (False ∧ p3)) → (p3 ∧ (((p3 ∨ p3) ∨ p5) ∧ p2)))) ∧ False)) → (p1 ∧ (True ∧ (p3 ∧ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h10 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h11 := h2 h10
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h15 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h14
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h16 := h2 h15
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229036052164294511983595830662 : ((p5 ∨ (False ∨ p5)) ∨ (p1 ∨ (p5 ∨ (p5 ∨ ((True → p2) → ((True ∨ (p3 ∧ (p5 ∧ ((True ∨ False) ∨ p3)))) ∨ ((p3 ∨ True) ∧ True))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58404467699487752639520463180 : (((p2 ∨ False) ∧ (p5 ∨ ((((p4 → p3) → ((((((p1 ∧ p3) ∧ p3) ∨ p3) ∧ True) ∧ False) ∨ (p2 ∨ p2))) → (p5 ∧ p3)) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2798890242119726087508013471 : ((False ∨ (p4 ∧ (False ∧ p2))) ∨ ((True ∨ ((((p1 ∧ (True ∨ p3)) → (p3 → p4)) ∧ p4) ∨ p3)) ∧ ((True → (p4 ∨ True)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744492729983478066051381793677 : ((((p2 ∧ p2) → ((p2 → (((((p4 ∧ True) → p5) ∧ p2) ∧ (p5 ∨ (False → (p5 ∨ (p1 ∨ (p2 ∧ (True ∧ p4))))))) ∨ p5)) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338996958574893113446192578626 : (p1 → (True ∧ (((((p3 ∧ p5) ∧ True) ∧ p2) ∨ (((p2 ∧ ((((p1 ∧ p2) ∧ (p3 ∨ p3)) → p5) ∧ (False ∨ p4))) ∨ p5) ∧ p3)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234095261184683209826851632156 : ((True → (p4 ∧ p3)) → (p2 ∨ ((p3 ∨ p3) → ((((False → p2) → (p5 ∧ ((p5 → p3) → p5))) → ((p2 ∧ p2) ∧ p2)) ∨ (True → True))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190352629379754254469925480649 : (((((p1 ∧ p3) → False) → (p3 ∧ (p3 ∨ p4))) ∨ p5) ∨ (((((p5 ∨ False) → p4) → True) ∧ True) ∧ ((p1 ∧ (p4 ∨ p5)) → (False ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
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
theorem thm_5_vars_114166091524754533676090712117 : ((((p3 ∧ ((p4 ∧ (p5 ∧ ((True → p3) ∨ ((p3 ∨ (False ∧ p4)) ∨ (p3 ∨ p1))))) ∧ p1)) → p2) → (p1 ∧ (p5 ∨ True))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61276636069223163870415023841 : ((False ∧ (p3 ∨ (((p4 ∧ ((((p4 → p1) ∧ (p5 ∧ p2)) → p1) ∧ p5)) ∨ p3) ∨ ((False → (p5 → p1)) ∧ ((p5 ∨ p3) ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617059238124841262407810101242 : ((((((False ∨ False) ∧ (p4 ∨ (p4 ∧ (p3 → True)))) ∧ (((((p3 → (True ∨ (p3 ∧ (p4 ∧ p2)))) → p3) ∨ p3) ∧ p5) ∧ True)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_669670507155213778455820829558 : ((((((False ∨ ((p3 ∨ ((True ∧ (p3 ∨ p1)) → False)) ∨ (p2 → True))) ∨ (True ∨ p2)) → ((True ∧ p3) ∧ p5)) ∨ (p5 → (p3 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323474305737946458457862786332 : (p5 ∨ ((((p5 ∨ ((p4 → (p3 → (p3 → False))) → (((p4 ∧ ((p5 ∧ p5) → p2)) ∧ p4) ∨ p3))) ∨ True) ∨ p2) ∨ ((p4 ∧ p5) → p3))) := by
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
theorem thm_5_vars_248652329172458273381074181062 : ((p3 ∨ p1) ∨ (((p2 ∨ p5) ∨ p2) ∨ (False → ((p1 ∧ (((p5 ∨ ((p5 ∧ True) ∧ True)) ∨ (p5 ∧ ((p4 ∧ True) ∨ p4))) ∨ p4)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178865937068796797656132302474 : (((p2 → (p1 → p4)) → ((p3 ∧ (p3 ∨ ((p3 → p5) ∨ p1))) ∧ True)) ∨ ((((False ∧ p3) → p4) ∧ (False ∨ ((p3 ∧ p3) ∨ True))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804805463971148077590460817915 : (((p3 → ((True ∧ False) ∧ (((p1 ∧ ((False → (p1 ∨ (True → p3))) ∨ (p1 → p4))) ∨ p5) → ((p4 ∧ ((p3 → True) ∧ False)) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148442533575494938470814476496 : (((p3 → ((((False → p5) → False) ∧ False) → ((True → (False ∧ p4)) → p1))) → (p2 ∧ (p1 → (p1 ∧ p3)))) ∨ ((True ∧ False) → (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250991721396674491244216897335 : ((p1 → p5) ∨ ((((False ∨ (p1 → (p1 ∧ p5))) ∧ (p4 ∨ p1)) ∧ ((p2 ∧ (((((False → False) → p2) → True) → True) ∨ p4)) ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57696432138466807944120482900 : ((((False ∧ p1) → False) → (((p1 ∨ (p1 ∨ p1)) ∨ (True ∨ ((p3 ∨ p5) → False))) → ((False → (p1 ∧ (p1 ∧ (p2 → p1)))) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324414591095135546345493431245 : (p5 ∨ ((p1 ∧ (p2 ∨ ((p4 → p5) ∧ p1))) → (((((p2 → True) → ((True ∨ p1) → p5)) ∧ p4) ∧ ((True → (p4 ∧ p3)) → False)) ∨ p1))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808694537973269986531158861419 : (((p4 → (p2 → ((((p5 ∨ (p5 ∨ p1)) ∧ ((True ∧ p3) ∧ (p1 ∧ ((p2 ∨ False) → p3)))) ∧ (p2 ∨ (p3 → p1))) → (False ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133863573937255842824850104103 : (((p2 ∧ ((((p5 ∨ False) → (True → ((p1 → True) → False))) → True) ∧ (p2 → ((p3 ∨ True) → (False ∨ p1))))) ∧ True) ∨ (p4 → (p4 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140757423150896584172508689489 : ((((p4 → False) → (False ∨ (p1 ∨ ((p1 ∧ ((p1 ∨ p2) → p3)) ∧ p4)))) → ((True → (False → (p2 ∨ p3))) ∧ p5)) → ((p3 ∧ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310112943630612833355741880585 : (p2 ∨ (((((True → p5) → ((p4 ∨ (p5 → p1)) → (True ∧ p1))) ∧ p3) ∨ False) ∨ ((p3 → p4) ∨ (True ∨ (((p4 → p4) ∨ p1) ∧ p3))))) := by
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
theorem thm_5_vars_263926936982725571191776132021 : (True ∧ ((((p4 ∧ True) ∧ True) → (False → ((p1 → ((p2 ∧ p1) → p4)) ∨ True))) → ((p4 → (p1 ∧ (((False → True) → p4) → True))) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110707559455043938471243384207 : ((((((p3 ∨ (p5 ∧ p2)) ∨ (p2 → (p3 ∨ (((p3 ∨ (p1 ∨ p5)) ∧ (p1 ∧ (False ∨ False))) → p1)))) ∨ True) ∧ p4) ∧ p5) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745018384691784874359241217539 : ((((p4 ∧ p1) → (((p2 ∨ p3) ∨ p4) → ((((((p1 ∧ ((p2 ∨ ((True ∨ p1) → p1)) ∨ p2)) ∧ p3) ∧ True) ∧ p5) → False) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200254770464069297690365512050 : (((False ∧ (True → p2)) → ((p2 ∧ p1) ∧ p2)) → ((((p2 → (p2 → ((p1 → p3) ∨ True))) → p4) ∨ (False → (False → True))) ∨ (False → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309841816190007344468983516364 : (p2 ∨ ((((p3 ∨ (((p5 ∧ (p5 → p5)) ∨ True) ∨ p2)) → ((False ∧ p4) → p4)) ∨ ((p1 → p2) ∧ p5)) → ((p3 → p5) ∨ (p3 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258402601027782368788766767318 : ((p5 ∨ p1) → ((p1 ∨ (((p2 ∨ ((((p3 ∧ True) ∨ (p2 → p1)) ∧ (p5 ∨ (p5 ∨ p3))) ∨ p4)) → p4) ∨ (False → (p5 ∨ p3)))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309779108414454728047501935597 : (p2 ∨ ((((True → (False ∧ (p4 ∨ (p3 → p2)))) ∨ ((p2 ∨ ((True → p4) ∨ True)) ∨ (True → p3))) ∧ p3) ∨ (True ∨ (p3 ∨ (p3 ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78541136579398888268460658058 : (((((p3 ∨ p1) ∨ (False → ((p4 ∧ ((((p3 ∧ ((p1 → p3) ∨ False)) ∨ p3) ∧ p5) ∨ p1)) ∧ (p4 → p4)))) → False) ∧ (p3 → True)) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p3 ∨ p1) ∨ (False → ((p4 ∧ ((((p3 ∧ ((p1 → p3) ∨ False)) ∨ p3) ∧ p5) ∨ p1)) ∧ (p4 → p4)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h5
    -- False on the left can always be used.
    apply False.elim h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180285649984146918185530972014 : (((p5 → ((True ∨ False) → ((((p3 ∧ p2) → p3) ∧ p1) ∧ p1))) → False) → (True → ((p1 ∧ ((((p2 ∧ p2) ∨ p5) → p2) ∨ False)) → p3))) := by
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
  cases h5
  case inl h6 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : (p5 → ((True ∨ False) → ((((p3 ∧ p2) → p3) ∧ p1) ∧ p1))) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h17 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h18 =>
        -- False on the left can always be used.
        apply False.elim h18
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h19 := h1 h7
    -- False on the left can always be used.
    apply False.elim h19
  case inr h20 =>
    -- False on the left can always be used.
    apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299294194147420398302884125597 : (False ∨ (((((p5 ∨ p2) → ((p1 ∨ (p2 ∨ False)) ∨ p3)) ∨ p5) ∧ ((True ∧ p3) ∨ (((((p3 ∧ p5) → True) → p2) → False) → True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330894183253549439172973603790 : (True → (p3 → (p3 → (p4 ∨ (p3 ∧ (((p1 ∧ ((False ∨ p5) ∨ p1)) → p4) ∨ (((p2 ∨ p1) ∨ ((p5 ∨ p2) ∨ p3)) ∧ (p1 → True)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133635764836135485787887985373 : ((((p4 ∨ (((p1 ∨ p4) ∨ (p4 → p2)) ∧ ((((p1 → (p3 ∨ p1)) ∨ p5) ∨ (p2 ∨ p2)) ∧ p2))) → p3) ∧ False) ∨ ((p5 ∨ p5) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198742586876306220866668368937 : ((True → ((((p4 ∧ False) ∨ False) ∧ p3) ∨ p4)) ∨ (((False ∨ (True ∨ (p4 ∨ (((p1 ∨ (p3 ∨ (p3 ∨ p2))) ∧ p3) → True)))) → p5) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ (True ∨ (p4 ∨ (((p1 ∨ (p3 ∨ (p3 ∨ p2))) ∧ p3) → True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136042272309210847713919792293 : (((p3 ∨ ((((p3 ∨ p2) ∧ p4) → p5) ∨ (p2 ∨ p1))) → (((p3 ∧ (p5 → p1)) ∧ ((True ∧ p3) ∨ False)) ∨ p3)) ∨ ((p1 → False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117311865240878421285906146422 : ((False ∧ (((((p2 ∧ (True ∧ ((False → p2) ∧ (p3 ∧ (p5 ∧ p3))))) ∨ p1) ∨ p3) ∨ p4) → ((p3 ∧ p3) ∧ (p4 → True)))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165172444356887707946246022576 : (((p2 ∧ ((p5 ∧ p4) ∨ ((p2 ∨ (p4 → p5)) ∨ ((p3 → p3) ∨ False)))) ∧ (p5 ∧ p1)) ∨ (False → ((p5 → (p2 ∧ p2)) → (p1 ∧ p5)))) := by
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
theorem thm_5_vars_178126915394467720049497712163 : ((((((p3 → p4) ∨ (p1 ∧ p2)) ∨ True) → (p5 ∧ (True → p1))) → p3) ∨ (True ∨ (p4 ∧ ((p3 ∨ False) → (((False → False) ∨ False) → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117431705903272191871281715839 : ((p1 ∧ ((((p2 ∨ p3) ∨ p2) ∨ (((p2 ∧ (p3 ∧ p5)) ∨ p2) ∨ (p4 ∨ p3))) ∧ ((p3 ∧ (p5 ∨ p4)) ∨ (False → p2)))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226131064230360068171678537422 : (((False ∨ p2) ∨ p1) ∨ ((((p1 ∨ True) → (False ∨ p1)) ∨ False) ∨ ((((p2 → ((False ∧ (p2 ∧ p5)) ∧ p3)) ∧ p1) ∧ p1) ∨ (False → p2)))) := by
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
theorem thm_5_vars_39603746519348129492839765538 : (((p2 ∨ ((((False ∧ p2) ∨ (p4 → p3)) ∧ (((False → (p5 ∨ (p3 ∨ p1))) → (p2 ∧ p4)) ∧ p3)) ∨ ((p2 → p1) → p2))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800825351890764167870385163863 : (((p2 → ((((p1 ∨ (((p2 ∨ p3) ∧ p5) ∨ (((p5 ∨ p1) ∨ p3) → p4))) ∧ ((p5 ∨ p4) ∨ (p1 ∨ p1))) ∨ p3) ∨ (p2 → True))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_54106459236270590585895006001 : (((p1 ∧ (p4 → ((True ∧ ((True → p2) ∧ p1)) ∨ p1))) → (p1 ∧ (((True ∨ p3) ∧ (True → ((p2 ∨ p5) → p3))) ∨ (p4 → p4)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192224222240202356264389541754 : ((((((p1 → p4) → p2) ∧ p2) ∧ (p3 → p3)) ∧ p5) → ((((p4 ∧ (False → False)) ∨ ((p3 → (p1 ∨ True)) ∧ (p3 ∨ False))) → p4) → p2)) := by
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
  let h7 := h5.left
  let h8 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717745777993260002962580279052 : ((((((p4 ∨ False) ∨ False) ∧ p4) ∨ ((p4 ∨ (p2 → (p4 ∧ (True ∧ ((True → ((p3 ∨ (True ∧ p4)) ∧ False)) → (False → p5)))))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48075597201334812535532754153 : ((((p3 ∨ ((False ∨ (p2 ∧ p2)) ∧ p2)) ∧ ((p2 → False) ∧ (False ∨ ((p5 ∧ (p2 → p3)) → ((p5 ∨ p3) ∨ p4))))) → (True → p3)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h4.left
      let h18 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
        have h21 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h17, we can now drive its conclusion.
        let h22 := h17 h21
        -- False on the left can always be used.
        apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625878195168501437940534229487 : ((((p2 → ((((True ∨ True) ∨ ((p2 → ((p3 ∧ ((p3 ∨ p5) ∧ True)) → (p2 ∧ (False ∨ p5)))) → p4)) → (p2 ∧ p1)) ∨ False)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112113486997563795458275663838 : ((((p2 → True) → (((((p5 ∨ p5) ∨ ((((True ∨ p3) ∧ True) ∨ p1) → True)) → p1) → (p5 ∨ p1)) ∧ (p1 ∨ p1))) ∨ True) ∨ (p3 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43229114270041116758814911074 : ((((p1 ∨ (((p2 → True) ∨ ((p3 ∧ ((((p3 → True) ∨ ((p3 ∧ False) ∨ True)) ∧ (p2 ∨ p4)) ∧ False)) → p1)) ∧ p4)) ∧ True) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324641519432792399122819404931 : (p5 ∨ (((p2 → False) ∧ p5) ∨ ((((True → ((p5 → True) ∧ True)) ∨ p3) → ((((p2 ∧ (p3 → False)) → p3) ∨ p4) ∧ False)) → (p4 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True → ((p5 → True) ∧ True)) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : ((True → ((p5 → True) ∧ True)) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h7
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308544608216957297469273915602 : (p2 ∨ ((((p1 ∧ False) ∨ (p1 → (((p3 ∧ p2) ∨ True) ∨ p2))) ∨ ((((True ∨ (False ∨ p1)) ∧ (True ∧ p4)) ∨ p4) → (p5 → p5))) ∨ p4)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150921747978033197146589124748 : ((((False → False) ∨ (True → (((p5 ∧ True) ∧ (p4 → ((p2 ∨ p2) ∧ (p4 ∨ p5)))) → (p3 ∨ False)))) ∨ p4) → (((p5 ∨ p4) → p2) ∨ True)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62801461773157601691090254858 : ((p4 ∧ (((p2 → (True ∧ p4)) → (p5 ∨ ((p5 ∨ p3) ∧ (p1 ∧ (p2 ∧ True))))) ∧ ((False → (p2 ∨ ((p3 → p4) ∧ p4))) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204366410844890054926939798521 : (((p3 ∨ ((p1 ∧ True) ∧ True)) ∧ p4) ∨ (p1 ∨ (p3 ∨ ((((p2 ∨ (p4 ∧ p5)) → ((p3 ∨ (p1 → (False ∧ p4))) ∨ False)) → p3) ∨ True)))) := by
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
theorem thm_5_vars_601227043287718715085132783022 : ((((p2 ∧ ((p3 ∧ (((p4 → p2) ∧ (p5 ∨ ((p2 → p4) → ((False ∧ p4) → p1)))) ∨ (p1 → ((True ∧ p4) ∧ p3)))) → p5)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42318965818878114362066290150 : (((p2 ∧ (p2 ∧ (((p1 ∧ False) → (p3 ∧ ((((p3 ∨ p3) ∨ p1) → ((p2 ∨ p2) ∧ p2)) ∧ ((False ∧ p5) ∨ p1)))) → p5))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123950886708826334858917087443 : (((p2 ∨ ((False ∧ (True ∧ ((p4 ∨ p1) ∨ p2))) ∧ (p4 → True))) ∧ (p2 → ((p1 → (((p5 ∨ True) → p5) ∧ p2)) ∧ False))) → (True ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800361517681187804197500253238 : (((p2 → (((p1 ∧ (p2 ∨ p4)) → (p5 → ((p3 → (True ∧ ((p5 ∧ (p4 ∧ (((p5 → True) → p4) → True))) ∧ False))) ∧ False))) ∨ p2)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329342937998834131526579647419 : (True → (((p4 → p3) ∨ False) → (((False ∧ (p5 → (p5 → ((p2 ∧ (p1 ∧ p5)) ∧ p2)))) ∧ False) ∨ (True ∨ (True ∨ ((p5 ∨ p2) → False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39582665602225545028774958796 : (((p1 ∨ (p1 ∨ ((((p2 ∧ p2) ∨ ((p3 → p1) ∧ p2)) ∧ True) ∨ (((p3 → p5) → (p2 → True)) ∨ ((p4 ∧ p4) ∧ p4))))) ∧ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191593665313268741179959159961 : ((p2 ∧ (p1 → ((p5 ∨ (False ∧ (p3 ∧ p1))) ∨ p5))) ∨ ((p4 ∧ p5) ∨ ((False ∧ ((p2 ∨ p2) ∨ (p4 ∨ (False ∨ p1)))) → (p4 → p4)))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181504862004378765675842913845 : ((p5 ∨ ((p1 ∨ p4) ∨ ((((p1 ∨ p4) → (False ∧ p3)) ∨ p3) ∨ p5))) → (((p5 → (True ∧ p3)) ∧ (((True → p2) ∨ p5) ∧ p4)) ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
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
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175565842924664270408176855011 : ((p5 → ((p2 → p4) ∧ (p1 → (((((p3 → p4) ∧ p2) ∧ p3) → False) ∨ False)))) → ((False ∧ p4) ∨ ((False → ((p2 → p5) ∧ p2)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192155409499546945731043187960 : ((((((True ∨ p2) ∨ (p3 ∨ False)) → False) ∧ p4) ∧ p2) → (((True ∧ False) ∧ (((p5 ∧ p4) → p5) ∧ False)) ∨ (p5 ∨ ((p4 ∧ p5) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((True ∨ p2) ∨ (p3 ∨ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713665068152857327364835995297 : ((((((p5 ∧ True) → (True ∧ p5)) ∧ True) → (((True ∧ (((p1 ∧ True) ∨ p3) ∨ (True ∧ p2))) ∧ (((p5 ∨ True) ∨ p2) ∨ p3)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151258401786023304381322268408 : ((((p1 → p3) → ((True ∨ ((p4 ∧ p1) → p1)) → (((p5 → p5) → (True → (p5 ∨ True))) ∨ p3))) → p1) → (p1 ∧ (p3 ∨ (p5 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 → p3) → ((True ∨ ((p4 ∧ p1) → p1)) → (((p5 → p5) → (True → (p5 ∨ True))) ∨ p3))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h11
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325795146766768369791039783928 : (p5 ∨ (p3 ∨ (((((p4 ∧ (p3 → (p3 ∧ True))) → (p2 → p3)) → (True → (False ∧ p3))) ∨ ((False ∧ ((p2 ∧ p1) ∨ False)) ∧ True)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135117872384080206207661219677 : ((((p4 ∨ p3) ∨ ((p4 ∨ p5) ∨ ((p1 → (p3 ∧ (False → (p5 ∧ ((p5 ∧ p1) ∨ False))))) ∧ p1))) ∨ (False → p1)) ∨ ((False ∧ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249618751793586745879026883757 : ((p5 ∨ p3) ∨ ((((True ∧ p4) → False) ∨ (p5 ∧ (p5 ∧ p2))) ∨ (((p3 ∨ (True ∨ p1)) ∧ (((p2 ∨ p3) ∨ True) ∨ (p2 ∨ p4))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



