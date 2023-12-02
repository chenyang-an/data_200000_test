variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747423668711844906943813326465 : ((((True → True) → (False ∧ ((((False ∨ p3) ∧ p2) ∨ ((((((True ∨ True) ∧ p4) ∨ p4) ∨ p3) ∨ (p2 ∨ (p4 ∨ p1))) ∨ p5)) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38757271782449418975126613025 : (((((p5 ∨ True) → (p5 ∧ True)) ∧ ((((p1 ∨ (p4 ∧ p1)) ∨ (p4 → (p4 ∨ p4))) ∧ ((True ∧ (p3 ∧ True)) ∨ p1)) ∧ True)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180731809468247485333476818420 : (((((p4 → p1) → p2) ∧ p4) ∨ (p5 → (p3 ∨ ((p3 ∧ p4) → p3)))) → (((p5 ∨ (p5 ∧ p5)) → p3) → (((p4 ∧ p3) ∨ p5) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : (p5 ∨ (p5 ∧ p5)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h16 := h2 h15
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h18 : (p5 ∨ (p5 ∧ p5)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h19 := h2 h18
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53516844411866984600289887112 : (((False → (((p1 ∨ ((False → p2) ∧ p4)) → p4) ∨ (p2 ∧ p3))) → ((p5 ∨ (p4 ∨ p3)) → (((p5 ∧ (p1 → True)) ∧ p3) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197489880368859038227803251097 : (((p1 ∧ ((False ∨ p5) ∨ p5)) ∧ (True → False)) ∨ (((True ∧ ((p3 ∨ (False ∧ p5)) ∧ (p2 → (False ∨ (p5 ∨ (p2 ∨ True)))))) ∧ p5) → p3)) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117580486391168764842340099225 : ((p2 ∧ ((p5 ∧ p4) → ((p3 ∨ (p5 → (p1 → p1))) → ((p5 ∧ p1) ∧ (p3 → (p1 ∨ ((False ∧ False) → (p2 ∨ False)))))))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300670472117009061879721082922 : (False ∨ (((((p2 → (p5 ∧ p1)) ∧ (p2 ∧ p5)) ∧ (p3 → (((p1 ∨ False) → False) ∧ p1))) → p1) ∨ (p2 ∨ ((False ∨ p5) ∨ (p1 ∧ True))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147589273559563031885452420540 : ((((((((p3 ∧ False) → p5) ∨ (False ∨ (((p2 ∨ True) → (True ∧ p3)) ∨ p5))) ∧ p1) ∨ p5) ∨ p5) → p4) ∨ (p2 ∨ (p2 → (p1 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231564564668273056713868986648 : (((p5 → p2) ∨ p3) → ((((p5 ∧ ((p5 → p4) → (True ∧ p1))) → p5) → p1) ∨ ((False ∧ (p5 ∨ True)) → ((p4 → p2) → (p2 ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- False on the left can always be used.
    apply False.elim h12
    -- Conjunctions on the left can always be decomposed.
    let h14 := h10.left
    let h15 := h10.right
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158170220515997519087581614176 : (((((p2 ∨ False) → False) → p3) → (((True → ((((p2 ∨ False) ∧ p3) ∨ False) ∨ p1)) ∧ p5) ∨ True)) ∨ ((True ∧ (p3 → p4)) ∧ (p2 ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41756168002208987433497846882 : ((((((p5 ∧ False) → p3) → p3) ∨ (((p5 ∨ ((((True ∨ p4) ∧ p5) → p1) ∧ ((p4 ∧ p1) ∧ (p2 ∨ True)))) ∨ p1) → False)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205392047988247491631617243389 : ((((p2 ∧ p5) → p3) → (p4 → p2)) ∨ (((((p3 ∨ p3) → (p2 ∨ (False → p5))) ∨ p4) ∧ (False → p1)) ∨ (p2 → (True → (p4 → p5))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134194176307468720676600903468 : ((((((p5 ∨ p3) → p3) ∨ (((p1 ∨ p4) ∨ p3) ∨ p1)) ∧ ((p2 → (((p4 → p1) → False) → p1)) → p3)) ∨ True) ∨ ((p4 → False) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338994022108967727270569821489 : (p1 → (True ∧ ((((p1 ∨ (p2 → ((p4 ∧ p1) ∨ False))) → ((p3 → p4) → (((p5 ∧ False) → (p4 → p1)) ∧ (p2 ∧ p1)))) ∧ p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58442178753076222034047804078 : (((p3 ∨ False) ∧ (((p5 ∧ p3) → p2) ∧ (p3 ∨ (p4 ∧ (True → (p1 ∨ ((p4 ∨ p3) ∨ ((p4 ∧ (False ∨ p4)) ∨ (p1 ∧ False))))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181418115964954576247404602780 : ((p2 ∨ ((p3 ∨ True) → (((p4 → True) ∧ (p4 ∧ p1)) → (False ∨ p3)))) → ((p1 ∧ (((False → p2) → p2) ∨ ((p5 ∨ False) ∧ p2))) ∨ True)) := by
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
theorem thm_5_vars_245719325966742963207714762438 : ((p3 ∧ p2) ∨ ((False ∧ (((p1 ∨ p3) → (p5 ∨ (p1 → (p4 → (p5 → True))))) ∧ (((p3 ∨ (p5 ∧ False)) ∨ p3) ∧ False))) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41229800121130893129173178961 : (((((p2 ∧ (p5 ∨ True)) → (((True ∧ (((p2 ∨ p2) ∨ p4) ∧ False)) ∧ (p5 → True)) ∨ False)) ∧ ((True ∨ (False ∨ p4)) → True)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8993000306736142411819997550 : ((((p5 → (((p2 → p1) → p1) → (((p4 → (p1 ∨ p2)) → p5) → (p4 → False)))) ∨ (((False ∨ p2) ∨ (False → False)) ∧ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314237643617895181359493004729 : (p3 ∨ ((((p5 ∧ False) → (((False ∧ (p2 → (p3 ∧ p5))) ∧ p2) ∧ ((((p2 ∧ p4) → p2) ∨ p3) ∧ True))) → p3) ∨ (p2 ∨ (True ∨ True)))) := by
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
theorem thm_5_vars_61108716536214941055451166723 : ((False ∧ ((((((True → True) ∧ (p4 ∧ (p4 ∧ p4))) ∧ True) → p2) ∧ True) ∧ ((p2 → (((p1 ∨ False) → (p2 → p5)) → p4)) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234613117010264596680160880800 : ((p3 → (p5 ∨ p4)) → (((((False ∧ p2) ∨ p4) → (p4 ∧ p2)) ∨ False) ∨ ((p2 → p1) → ((False ∧ p5) → (p2 → ((p5 ∧ p1) ∧ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h7 := h3.left
  let h8 := h3.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h9 := h3.left
  let h10 := h3.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136031159227256386040214934820 : ((((True ∨ (p4 ∨ p1)) → ((p1 ∨ p1) ∧ (p1 → False))) → ((p2 → (p3 ∨ (p5 → (True ∧ (p5 ∧ False))))) ∨ p2)) ∨ ((False → p3) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110766068550344016416287731092 : ((((True → ((((True ∨ False) ∧ (p4 ∨ p4)) ∧ (((True → True) ∨ (p3 ∨ (p5 ∨ False))) ∨ p2)) ∨ (False ∧ p4))) ∧ p3) ∧ p4) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801333511618539059115836288107 : (((p2 → ((p4 ∨ (p3 ∨ ((False ∧ p2) ∨ ((True → (p1 → (p1 → False))) → p4)))) → ((((p4 ∨ p1) ∧ (True ∧ p4)) ∨ True) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60251437719999739790970418907 : (((False → False) → ((p1 ∨ (p4 ∧ (p5 ∨ (True → (((False → ((p4 → (p5 → p2)) ∨ (p1 ∧ True))) ∧ p3) → p5))))) → (p3 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136000653645105400074281104289 : (((p5 ∧ ((p5 ∨ (p3 → True)) → ((False ∧ True) ∨ p1))) ∨ ((p5 → (p3 ∧ True)) → ((False ∧ False) → (True ∨ True)))) ∨ (True ∧ (True ∧ p3))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39333781167001639862911559535 : (((p2 ∧ ((((p2 → False) ∨ p4) ∨ (True ∧ (True → p2))) ∨ ((True → True) → (((p3 ∧ p3) → True) ∧ ((p2 → p4) ∧ p3))))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49025420401233707002507101171 : (((((p1 ∧ (p2 → (p4 ∨ ((p1 ∧ False) ∧ p5)))) → ((p3 ∧ ((p3 ∧ (p3 ∨ p2)) ∨ p3)) → p4)) → p1) ∨ ((p3 → True) ∧ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595481501070154188342219637466 : ((((((((p4 ∧ p3) → p2) ∨ p2) → (p4 ∧ ((False ∨ p4) ∧ p1))) ∨ (((p2 ∧ ((p4 ∧ True) → (p3 → True))) ∨ p3) ∨ p5)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130157781096848641595388466887 : ((((p1 ∨ p4) ∨ ((p2 ∧ ((p2 ∧ p5) ∨ ((p3 ∧ (p4 ∨ p1)) → ((p1 ∨ p2) → False)))) → False)) ∨ (False → p4)) ∧ ((p1 ∨ p1) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215382891885440292496101580094 : ((p2 ∧ (True ∧ (p2 ∨ p1))) ∨ ((False ∧ False) ∨ ((((p2 ∨ ((p4 ∨ p2) ∧ (p3 → p1))) ∨ p2) ∧ False) ∨ (True ∨ (p3 ∨ (True ∨ True)))))) := by
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
theorem thm_5_vars_782971948162906700306473963241 : (((p3 ∨ ((((p1 → ((True ∨ p4) ∧ p2)) → ((((p2 ∨ p1) ∨ ((p2 ∧ p4) → p4)) ∧ (False → p3)) ∧ p4)) ∨ True) ∨ (p3 ∨ p1))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753678080753617859031516372125 : (((False ∧ ((p1 → ((p2 ∨ p4) ∧ ((p1 → p5) ∨ (((False ∨ p5) ∧ p1) → p2)))) ∧ ((p2 ∧ (((p3 ∨ p3) ∧ p2) → p3)) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350573277565670823420955504541 : (p4 → (((((((p3 → True) ∧ True) ∨ True) → True) ∧ (True → p3)) ∧ (True → (p2 ∨ ((p5 ∨ (p3 ∨ ((p2 ∧ p1) ∨ p3))) → p5)))) → p3)) := by
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137686843306874889935474716491 : ((p1 ∨ ((False ∧ ((p3 ∧ True) → ((p4 ∨ (True ∧ ((True → (p2 → (True ∧ (False ∧ p1)))) ∨ True))) ∧ False))) ∨ True)) ∨ ((p4 ∧ p2) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312240718436741151391476893879 : (p2 ∨ (p1 → ((((p4 → ((p3 ∨ (p5 ∨ (p3 → p2))) → p2)) ∧ p4) → (True → ((p5 → p2) → ((p4 ∨ True) → p2)))) ∨ (p5 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317023981732887994934870625666 : (p3 ∨ (p3 → (p2 → ((True ∨ (p5 ∧ (p2 → p5))) ∧ (((True ∧ (((p4 → True) ∧ (p2 → (p1 ∨ (p5 ∨ p5)))) ∧ p1)) ∨ p4) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46922873757361123030353477786 : ((((((p2 ∧ True) → p4) ∧ (True → ((False ∧ ((p3 ∨ ((p4 → p1) → (p2 ∧ (p4 ∨ p3)))) ∧ p5)) ∨ True))) ∨ False) ∨ (True ∨ False)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633649135925719463752045021815 : ((((((p5 ∧ p2) → ((False ∨ p5) ∨ (False ∨ (p2 → ((p4 → ((False → False) ∧ (p4 ∧ p2))) ∧ (p4 ∨ False)))))) ∨ (False ∧ p3)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49253117391461700578028437089 : (((True ∧ (False ∨ (((p3 ∨ p2) → ((True → (p4 ∨ p2)) ∨ (p1 ∧ p2))) ∧ ((p3 → (p4 ∨ p2)) ∧ False)))) ∨ (p3 → (p4 → p3))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338101543985779644027088908856 : (p1 → ((((p2 ∧ p3) ∧ p2) ∨ (p1 ∧ (True → True))) ∧ (((p2 → p5) ∨ (p4 ∨ ((p2 ∨ ((p4 ∧ p4) ∧ p2)) → (p3 ∨ p4)))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340967317244429125158929930619 : (p2 → (((p1 ∨ False) ∧ ((p3 → (((p5 → p3) → (False ∧ ((p2 → p3) ∨ ((p1 ∨ p4) ∨ p4)))) ∨ (False ∨ (True → p3)))) → p1)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337353944000918051552070657507 : (p1 → (((p3 ∨ ((((p3 → (False ∨ p3)) ∧ (((True → (p2 ∧ p1)) ∧ p5) → p3)) ∨ (False → p1)) ∨ p4)) → False) ∨ (p5 → (p5 ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259721306090571574519984331284 : ((p1 → p1) → (p4 ∨ (((True → ((((True → p4) → p1) ∨ p5) ∧ p3)) → ((p2 ∨ p5) ∨ (((p2 → p3) ∧ False) ∨ False))) ∨ (p1 → p1)))) := by
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
theorem thm_5_vars_191863799765835358509195061564 : ((p4 ∨ (((p4 ∨ (p3 ∧ (p4 ∨ p4))) ∨ p5) → p4)) ∨ ((((((p4 → p4) ∨ p1) ∧ p1) → (True ∧ p5)) → ((p4 ∨ p3) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154306660462285857373194302981 : (((p3 ∧ ((((p1 → p3) ∧ (((p2 ∨ (p5 → p3)) → False) ∧ (p3 ∨ False))) ∨ p5) ∨ True)) ∨ True) ∧ (False → ((p2 ∧ True) ∧ (p5 ∧ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689749329865881081728846911829 : (((((p2 ∧ (p3 ∧ p5)) ∨ (p3 ∧ (True ∨ ((False → (True → False)) ∨ (False ∧ p1))))) ∨ (((p5 ∨ p4) ∨ p4) ∨ ((p5 ∧ p4) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150755642240789901956177912038 : ((((p5 ∧ (((p2 → (p4 ∨ p4)) → ((False ∨ (False ∨ False)) ∧ p1)) ∧ ((p1 ∧ True) → p3))) ∨ False) ∨ p3) → ((p3 ∨ p5) ∨ (p4 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299266547094928813028544882183 : (False ∨ ((((p2 ∧ p3) ∧ (p2 ∧ (p2 ∨ ((p3 ∧ (p2 ∨ (p5 ∨ False))) ∧ (p2 ∧ p1))))) ∧ ((p1 → (p4 → (p4 → p3))) ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58645342640301565417724163590 : (((p1 → p1) ∧ (True ∧ (p3 ∨ (((True → ((((((True ∨ (p1 → p5)) ∧ p2) → p3) → True) ∧ p4) ∧ p3)) ∧ (p2 ∧ p1)) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116183186515708186205649384210 : (((p4 → (True → True)) ∧ ((p1 ∨ (((((((p4 → True) → True) → (p4 ∧ (p1 ∧ p3))) ∨ p5) ∧ True) ∨ p2) ∧ p4)) ∨ True)) ∨ (p3 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323652056655752600147506913792 : (p5 ∨ (((((True ∧ ((p1 ∧ (((True → True) → p3) → p1)) ∧ p1)) ∨ False) ∧ (p5 → (p4 ∧ p3))) ∨ True) ∨ (p1 ∨ ((p1 → True) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342158659965594264566440129665 : (p2 → (((p3 ∨ ((False ∨ (True ∨ p5)) → ((True ∧ (p3 ∧ False)) ∧ p4))) ∨ (((p5 ∨ p3) → False) ∧ False)) ∨ ((True → (p3 ∨ True)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245210631520871489589445144845 : ((p2 ∧ False) ∨ (p1 → (p2 → ((((((p2 ∧ (p1 → (((p4 ∨ (p3 ∨ True)) ∨ p1) ∧ p4))) → p3) ∨ p1) ∨ p5) → p4) ∨ (True ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606675473682612009544028423137 : (((((((p4 ∧ ((p3 → p5) ∨ ((p3 → ((p2 ∨ p2) → (p3 ∨ p3))) → p1))) ∨ (p4 ∧ (p2 ∧ p3))) ∧ (p3 ∨ False)) ∧ p5) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171516495010607884005815030874 : (((((p1 ∨ p5) → (p4 → ((p4 ∨ (p3 → (p4 → p4))) → p3))) ∧ True) ∨ True) ∨ ((False → ((p4 ∧ (True ∧ p3)) ∧ p1)) ∨ (True → p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46803068251027646216249495352 : ((((((p3 ∨ (p5 ∧ (((p2 ∨ p3) ∧ (p1 ∧ p2)) ∨ (p4 ∧ p1)))) → ((p1 → (True → p1)) ∧ p2)) ∧ p4) ∧ p1) ∨ (p3 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196716474952492124223709354445 : ((((((True ∨ p5) ∨ True) → p5) → p2) ∧ p1) ∨ (p5 ∨ (((p4 ∨ ((p1 ∨ (p3 → p1)) → (p3 ∨ p1))) ∨ (False → p4)) ∨ (True ∨ p2)))) := by
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
theorem thm_5_vars_47223768010245458605385669148 : ((((((p3 ∨ ((p1 → p4) ∨ p2)) → False) ∨ p2) ∧ (((p3 ∨ (False → True)) → ((p2 ∨ False) ∧ (p4 ∧ p1))) ∧ False)) ∨ (True ∨ p3)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175140970197009026747636011150 : ((p5 ∧ ((((p1 ∧ p1) ∧ False) ∧ (p1 → True)) ∨ (p3 ∨ (p5 ∨ (p1 → p1))))) → ((False ∨ p5) ∧ (((p3 → (p3 ∧ p4)) ∧ p2) ∨ True))) := by
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
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h19.left
    let h22 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h23 := h21.left
    let h24 := h21.right
    -- False on the left can always be used.
    apply False.elim h22
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h26 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h29 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113306615280282708546538684505 : ((((False → (p4 → (p5 → p1))) ∧ ((p3 ∨ (p3 → (p4 ∨ (p5 ∨ p1)))) ∨ (p2 ∨ (p1 ∨ (p5 → False))))) ∧ (p2 ∨ True)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248848115943290370743747827402 : ((p3 ∨ p4) ∨ (p1 ∨ ((((p4 ∧ (((p4 → (((False → p2) ∨ p1) → (p1 ∧ False))) → (p5 ∧ False)) → (p2 ∧ p5))) ∨ False) → p5) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : ((p4 → (((False → p2) ∨ p1) → (p1 ∧ False))) → (p5 ∧ False)) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h7 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h8 := h6 h7
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : ((False → p2) ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h10
        -- False on the left can always be used.
        apply False.elim h10
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h11 := h8 h9
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h13 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h14 := h6 h13
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h15 : ((False → p2) ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h16
        -- False on the left can always be used.
        apply False.elim h16
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h17 := h14 h15
      -- We need to get the right conjuct of h17 based on <expert-advice>.
      let h18 := h17.right
      -- False on the left can always be used.
      apply False.elim h18
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h19 := h4 h5
    -- We need to get the right conjuct of h19 based on <expert-advice>.
    let h20 := h19.right
    -- One of the premise coincides with the conclusion.
    exact h20
  case inr h21 =>
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340767196825041790567152870099 : (p2 → (((p5 → (p3 ∨ (((False ∧ True) ∧ p5) ∨ (((p4 ∨ (True → ((True → p1) → ((True → p4) ∨ p5)))) ∨ p1) ∨ p4)))) ∨ p5) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111600776365695614519513975782 : (((((((p3 → p5) → ((p3 → ((((p2 ∨ False) → (p2 → p2)) ∨ p4) → (p4 ∨ p2))) ∨ True)) ∨ p5) ∧ True) ∨ False) ∨ p5) ∨ (p1 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38260841492837657702520522311 : ((((p1 ∨ (((((False ∨ ((p3 ∧ p2) ∧ p5)) → p1) → True) → ((p4 ∧ p2) ∨ p4)) ∨ p4)) ∧ (p3 → ((p2 ∨ True) ∧ p2))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191145480293729967922346023396 : ((((p4 ∨ p5) ∨ p5) ∨ ((p4 ∨ p4) ∨ (True ∨ p1))) ∨ (((p3 → p1) ∨ (((False ∧ p5) → p2) → (((p3 ∨ False) ∨ False) ∨ True))) → p4)) := by
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
theorem thm_5_vars_135336467199637133225369955223 : ((((p2 → (p3 ∧ p3)) ∨ ((((p4 ∨ p2) → p4) → (p4 ∧ p4)) ∧ (p2 → (True → p4)))) ∧ (p5 ∨ (p5 → p5))) ∨ ((p2 ∧ p2) → p2)) := by
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
theorem thm_5_vars_54889093139045427463328267336 : (((((True ∧ False) ∧ (False → p5)) ∨ p1) ∧ (p4 ∨ (p2 ∨ ((((p3 ∨ p1) ∧ (p5 ∨ ((p5 → True) → (True ∧ p5)))) → p5) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41682191531728541837395914216 : ((((p2 ∧ ((False ∨ (p5 ∨ False)) ∧ p3)) ∨ (((p4 ∨ (True → (p4 → (False ∧ p2)))) ∨ ((p5 ∨ (p5 → False)) → p3)) ∨ True)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778645934623296945012408416067 : (((p1 ∨ (p1 ∨ (p2 → (((((p5 → p2) ∧ (((((p4 → p2) ∨ False) → p4) ∨ p2) → p4)) ∨ (False ∧ p4)) ∧ (p3 → p2)) ∨ True)))) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219160679542340699854837403745 : ((False ∨ ((p2 → p3) ∧ p4)) → (((p5 ∧ (((p4 ∧ p2) ∧ (p1 ∨ p5)) ∧ (False ∧ (p5 ∧ (p1 ∧ False))))) ∧ ((False ∨ p1) ∨ p4)) ∨ p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316379873263253111203795675136 : (p3 ∨ (False ∨ ((True ∧ (p1 ∧ (((p2 ∧ ((((p2 → (((p3 ∧ p3) ∧ p3) ∧ p5)) ∧ p2) → p2) → p5)) ∨ p1) → p4))) → (p4 ∨ False)))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((p2 ∧ ((((p2 → (((p3 ∧ p3) ∧ p3) ∧ p5)) ∧ p2) → p2) → p5)) ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196979624250839715693584333225 : (((((p2 ∧ (p4 → p2)) → True) → p3) ∨ p3) ∨ (((((True ∧ False) ∧ p1) ∨ p2) ∨ ((p1 ∨ (p3 → ((p1 → p1) ∧ p1))) ∨ True)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165421358034264922267156041775 : (((((p3 ∧ True) ∨ (p2 ∧ (p1 → p1))) → (p4 ∧ (p3 → p2))) → (p5 ∧ (p3 → p1))) ∨ (p4 ∨ (((p2 → p3) ∧ p2) → (p2 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191827910273165524245975754919 : ((p3 ∨ ((((False → (p3 ∨ p2)) ∨ False) → p3) ∨ p3)) ∨ (((False ∧ True) ∧ (p1 ∧ (((False → (True → False)) ∨ p3) ∨ (p5 ∨ p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158374683786803065765771365053 : (((p5 ∨ p1) ∧ (((False ∨ p3) ∧ ((p4 → True) → (p4 → p4))) ∨ (True ∨ ((p1 → p4) ∨ p5)))) ∨ (((p3 → p3) → False) → (p2 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50883715066743871874009127638 : ((((((p5 → p4) → (p1 ∨ (p3 ∨ ((p2 ∨ p2) ∨ False)))) ∨ ((p5 → True) ∧ p5)) → p3) ∧ (((p3 ∧ (False ∧ False)) ∨ p3) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112034093073656348095064873225 : ((((p1 ∧ (True ∧ True)) ∨ ((p4 ∨ ((False ∨ p5) ∧ p1)) ∧ (((p2 ∨ ((p3 ∧ True) ∧ (p1 ∨ p5))) ∨ p4) ∨ p4))) ∨ p5) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119171744169612840120899835330 : ((p2 → ((p5 ∨ (p5 ∧ (p1 ∨ ((p4 ∧ True) ∧ (((p4 → p1) → p2) ∧ (((True ∨ p4) ∧ p5) ∨ (False → p5))))))) ∨ p5)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746828450194313776190164298406 : ((((p3 ∨ p5) → (((p5 ∨ p4) ∨ False) ∨ (p1 ∨ (((((p1 ∧ (p5 ∧ (True ∧ ((p4 ∨ p1) ∨ p4)))) ∨ p1) ∨ p3) ∧ False) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347209464280217103787848403324 : (p3 → ((p5 ∨ ((p1 ∧ p3) ∨ ((False ∨ (p1 ∨ (False ∨ p1))) ∨ p3))) ∨ ((p4 → p2) ∧ (((p5 ∨ ((p1 ∨ p4) ∨ p4)) ∨ p3) ∧ False)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673650406986418471689660372449 : ((((((False → p3) → p4) → ((p1 → ((p2 ∧ p4) ∧ (p3 ∨ (p4 ∨ p2)))) ∧ ((p2 ∧ (p4 → False)) → p2))) → ((p5 ∨ p5) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217387357534635800634821651683 : (((p5 ∨ (p4 → p4)) ∨ p2) → ((True → p3) → ((p4 ∨ p1) ∨ ((p5 ∧ (p3 → p3)) ∨ ((False ∨ False) → (p5 ∧ (True → (p2 ∧ p2)))))))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18
    -- Implications on the right can always be decomposed.
    intro h19
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h20 =>
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- False on the left can always be used.
      apply False.elim h21
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h22 =>
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147874762435783637229903475068 : (((p4 → ((p4 → (p4 ∨ ((((p2 ∧ False) ∨ False) → ((p2 ∧ True) ∨ p3)) → p3))) → (p3 → p1))) → p3) ∨ (((p5 → p1) ∧ False) → p2)) := by
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
theorem thm_5_vars_258628049737683342666707708614 : ((p5 ∨ p4) → (p4 ∨ ((p5 ∧ (((True ∧ p3) ∧ (((p1 ∧ (p1 → (((p1 ∧ p3) → (False → True)) → p2))) ∧ p5) ∨ p1)) ∨ False)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115584613576790715649839413608 : (((((p4 ∧ p4) → p5) → (p2 ∧ p4)) ∧ (False ∧ ((((False ∧ p3) → p1) → (p2 ∨ (p5 ∨ p3))) ∨ (p4 → (p3 → p4))))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205386236742127679149192769115 : ((((p4 → p1) ∨ p2) → (p5 ∨ p5)) ∨ (True ∧ ((p4 ∨ True) → ((p2 ∨ ((((True ∨ (p2 ∨ p4)) ∨ (p3 → p1)) ∨ True) ∨ p3)) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_324297770557621453866308036725 : (p5 ∨ ((((p1 → p4) → p2) ∨ (p1 ∨ (True ∧ p1))) → ((p4 ∧ False) ∨ (((p3 → (p3 ∨ (p5 ∨ (p5 ∨ p5)))) ∨ p5) ∨ (p1 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
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
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42913159298211586366454141347 : (((p3 → (p2 ∨ (((p4 ∨ p4) ∨ (p5 ∨ ((((True ∨ p1) ∨ p5) ∨ p3) → (True ∧ p1)))) ∨ ((False → (p5 ∧ True)) ∨ p5)))) ∨ p5) ∨ p5) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199369704538491826615449419872 : (((((p3 ∧ p2) ∨ False) ∨ (p1 ∨ p1)) ∨ p2) → (p4 ∨ ((((p3 ∧ (p5 ∨ ((False → (p2 ∨ p3)) → False))) ∨ True) ∨ True) ∨ (False → p2)))) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h5 := h4.left
        let h6 := h4.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- False on the left can always be used.
        apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261308325939481968327980914254 : ((p5 → False) → (((((((p1 → p5) ∨ p4) ∨ (True → p2)) ∧ (p2 ∧ (p5 ∧ ((p2 ∨ p3) ∧ ((p2 → False) ∨ True))))) ∧ True) → p4) ∧ True)) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h6.left
      let h10 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h16 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h17 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h11
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h18 := h1 h17
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h20 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h11
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h21 := h1 h20
          -- False on the left can always be used.
          apply False.elim h21
      case inr h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h23 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h24 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h11
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h25 := h1 h24
          -- False on the left can always be used.
          apply False.elim h25
        case inr h26 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h27 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h11
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h28 := h1 h27
          -- False on the left can always be used.
          apply False.elim h28
    case inr h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h6.left
      let h31 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- Conjunctions on the left can always be decomposed.
      let h34 := h33.left
      let h35 := h33.right
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h36 =>
        -- Disjunctions on the left can always be decomposed.
        cases h35
        case inl h37 =>
          -- One of the premise coincides with the conclusion.
          exact h29
        case inr h38 =>
          -- One of the premise coincides with the conclusion.
          exact h29
      case inr h39 =>
        -- Disjunctions on the left can always be decomposed.
        cases h35
        case inl h40 =>
          -- One of the premise coincides with the conclusion.
          exact h29
        case inr h41 =>
          -- One of the premise coincides with the conclusion.
          exact h29
  case inr h42 =>
    -- Conjunctions on the left can always be decomposed.
    let h43 := h6.left
    let h44 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h45 := h44.left
    let h46 := h44.right
    -- Conjunctions on the left can always be decomposed.
    let h47 := h46.left
    let h48 := h46.right
    -- Disjunctions on the left can always be decomposed.
    cases h47
    case inl h49 =>
      -- Disjunctions on the left can always be decomposed.
      cases h48
      case inl h50 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h51 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h45
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h52 := h1 h51
        -- False on the left can always be used.
        apply False.elim h52
      case inr h53 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h54 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h45
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h55 := h1 h54
        -- False on the left can always be used.
        apply False.elim h55
    case inr h56 =>
      -- Disjunctions on the left can always be decomposed.
      cases h48
      case inl h57 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h58 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h45
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h59 := h1 h58
        -- False on the left can always be used.
        apply False.elim h59
      case inr h60 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h61 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h45
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h62 := h1 h61
        -- False on the left can always be used.
        apply False.elim h62
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40360348315754955331328124840 : (((((((((p1 ∨ (((p4 → p3) ∨ p4) → p1)) ∨ p3) ∨ p5) ∨ p4) ∨ ((p3 → (p1 → (p2 → p3))) → p2)) → False) ∨ True) ∨ p2) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111981886743540609646678381078 : (((((False ∨ ((p2 ∨ p2) ∧ p2)) ∨ p3) → (False ∨ (p4 ∨ ((False ∨ (p1 → p5)) ∨ ((True ∨ p2) ∧ (True → False)))))) ∨ True) ∨ (p3 → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191042221488608085119142242668 : ((((False ∨ (False → True)) → p5) → ((p3 ∨ p3) ∧ p2)) ∨ (True ∨ ((((False → ((p1 → ((p1 → p4) ∨ p2)) ∨ True)) → p1) ∧ p4) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225526210503827129891122889663 : (((True → True) ∧ p4) ∨ ((((True ∨ True) ∨ p1) → p4) → ((((False → (p3 ∨ p2)) → p5) ∧ (False ∨ (p4 → (p3 → p2)))) ∨ (p2 ∨ True)))) := by
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
theorem thm_5_vars_48626801850125602808661465782 : ((((p4 ∧ ((False → (p2 ∧ (False ∨ (p3 → ((False → False) → (False ∨ p5)))))) → p1)) ∧ (True ∧ (p5 → p5))) ∧ ((p2 → p1) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208032180777359474652938668766 : (((False ∧ (p4 → p5)) ∨ (True → p4)) → (p4 → (((((((True → True) ∧ p5) ∧ p3) ∨ p1) ∨ (p5 ∧ (p5 ∨ p2))) ∧ (p4 → p2)) → p2))) := by
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
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- False on the left can always be used.
        apply False.elim h13
      case inr h15 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h16 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h17 := h5 h16
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- False on the left can always be used.
        apply False.elim h20
      case inr h22 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h23 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h24 := h5 h23
        -- One of the premise coincides with the conclusion.
        exact h24
  case inr h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h29 =>
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- False on the left can always be used.
        apply False.elim h30
      case inr h32 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h33 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h34 := h5 h33
        -- One of the premise coincides with the conclusion.
        exact h34
    case inr h35 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h36 =>
        -- Conjunctions on the left can always be decomposed.
        let h37 := h36.left
        let h38 := h36.right
        -- False on the left can always be used.
        apply False.elim h37
      case inr h39 =>
        -- One of the premise coincides with the conclusion.
        exact h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352281656722091348690161341798 : (p4 → (((p5 ∨ False) ∨ (False → True)) → ((((p4 ∧ p2) ∨ ((p1 ∨ (p4 → True)) ∨ ((p2 ∨ p5) ∧ p1))) ∧ ((p2 ∧ p2) ∨ p5)) ∨ p4))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354753689233425550287465417583 : (p5 → ((((True → p3) ∧ (((p1 ∨ p5) → (p2 → ((p2 ∧ p1) ∧ p5))) ∨ p2)) ∧ ((((p2 ∨ p5) → False) ∧ (p1 ∧ p1)) ∧ p4)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



