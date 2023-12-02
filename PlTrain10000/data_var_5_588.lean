variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810498317098509220017140018988 : (((p5 → ((False ∧ ((p2 ∧ p4) ∨ (p1 ∧ p4))) ∨ (p4 → ((False ∧ False) → (False → ((((p5 → p3) → p3) ∨ (p4 ∧ p5)) ∧ p2)))))) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115944319868003905036754812359 : (((p2 ∨ ((p1 → False) → p1)) ∨ (True ∧ ((((p2 ∨ ((True → p2) → p3)) → p4) ∧ (False ∧ p2)) ∨ (p2 → (p3 → p2))))) ∨ (p4 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258425796637340780761724988259 : ((p5 ∨ p1) → (((p2 ∧ (False ∨ (p5 → p4))) ∧ p5) ∨ ((((p5 → (False ∧ p5)) ∧ (p3 → (p1 ∨ (p5 ∨ (False ∨ p2))))) ∨ True) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133553948415313526037608414886 : ((((((p1 → (p2 ∨ (p3 → ((p3 ∧ p2) ∨ ((p5 ∧ (p3 ∨ p2)) ∨ (p5 ∨ True)))))) ∧ False) ∧ p4) ∨ p5) ∧ p2) ∨ ((False → p5) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40314451626542901304411781678 : ((((((p4 ∧ p1) ∨ (False ∨ ((((p4 ∧ (p3 ∧ (p5 ∧ (False ∨ False)))) → p1) ∧ p1) ∧ (p5 ∧ (p1 → p3))))) ∧ p5) ∨ p3) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260849655101294977802505022322 : ((p4 → True) → ((((p1 ∨ (p5 ∧ p1)) → ((((True ∧ p3) → p4) → p4) ∧ p5)) ∨ True) ∨ ((p5 ∧ (True ∧ ((True ∧ p4) → p4))) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804461481652730494952688753725 : (((p3 → ((((p2 → False) ∧ (p2 → (p1 ∧ p1))) ∧ True) ∨ (p5 ∨ (((False → (True → (p1 ∧ ((False ∧ p2) ∧ p4)))) ∧ p1) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52115399232780731438626200406 : (((((p3 → (p1 ∧ (p5 → ((False ∨ (True ∨ p5)) → p1)))) → (p2 ∧ False)) → p3) → ((p2 → ((p2 ∧ p1) ∨ p3)) ∨ (False → True))) ∨ p2) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263122662077824813349296303071 : (True ∧ (((p3 → ((p3 → p2) ∧ (p2 ∧ (((p4 ∧ False) ∧ p1) → p4)))) → (((p1 → p5) → ((p4 ∧ p5) → p1)) → p4)) ∨ (True → True))) := by
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
theorem thm_5_vars_198390985444680153070319483277 : ((p3 ∧ (p3 ∧ ((p4 → (p3 → p1)) ∨ p1))) ∨ (p3 ∨ ((p3 ∧ ((((True ∨ p5) ∨ p3) ∧ (p3 ∨ p2)) ∨ (p4 ∨ p5))) ∨ (False ∨ True)))) := by
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
theorem thm_5_vars_769033573466011217267053090619 : (((p5 ∧ ((p2 ∧ (p3 ∧ p3)) ∨ (((((((True ∧ p1) ∧ p2) → (p2 → (False ∧ (p4 ∨ p1)))) ∨ (p4 ∧ p3)) ∧ p3) → p1) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311260746391706713985070615815 : (p2 ∨ (True ∧ ((p1 → ((p2 ∧ p1) ∨ ((((p2 → (p5 → p5)) → (p1 ∧ p4)) → (p4 ∧ ((p2 → (p1 ∨ False)) ∧ False))) ∨ p1))) ∨ p5))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_91158081058199068764523237294 : (((p5 → False) ∧ ((p5 ∨ False) ∧ (p3 ∧ ((((p2 → p3) ∨ False) → (p4 ∨ (p5 → p3))) → (True ∧ (((p2 → False) ∧ False) → p5)))))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214401577428256915842973533123 : (((p1 → (True ∧ p3)) → p4) ∨ ((p2 ∨ p2) ∨ (False → ((p2 ∨ (((p1 ∧ (p2 → p3)) ∨ False) ∧ ((False ∧ p5) ∨ (p1 → p1)))) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692589180136580034170620700376 : (((((p1 ∨ ((p2 ∨ (False → p3)) → (p2 ∧ p1))) ∧ (p2 ∧ (p4 → p5))) ∧ (p2 ∨ (p5 ∨ ((p2 → (p4 ∨ (p2 ∧ p1))) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228531258489194246379673559292 : ((p1 ∨ (p2 ∧ False)) ∨ ((True → (p1 ∧ ((p3 → False) → ((False ∨ p1) ∨ ((p4 ∧ False) ∨ p3))))) ∨ (False → (((p5 ∨ p3) ∧ p4) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h1
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200882221570596866469575990127 : ((False ∨ (((p5 ∧ p3) ∨ p4) ∧ (True ∨ p1))) → ((((True → (p1 → p5)) → (True ∧ p3)) → ((p1 ∨ p5) ∧ (False ∧ p4))) → (p3 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h11 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h12 : ((True → (p1 → p5)) → (True ∧ p3)) := by
          -- Implications on the right can always be decomposed.
          intro h13
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h14 := h2 h12
        -- We need to get the right conjuct of h14 based on <expert-advice>.
        let h15 := h14.right
        -- We need to get the left conjuct of h15 based on <expert-advice>.
        let h16 := h15.left
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h18 : ((True → (p1 → p5)) → (True ∧ p3)) := by
          -- Implications on the right can always be decomposed.
          intro h19
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h20 := h2 h18
        -- We need to get the right conjuct of h20 based on <expert-advice>.
        let h21 := h20.right
        -- We need to get the left conjuct of h21 based on <expert-advice>.
        let h22 := h21.left
        -- False on the left can always be used.
        apply False.elim h22
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h24 =>
        -- One of the premise coincides with the conclusion.
        exact h23
      case inr h25 =>
        -- One of the premise coincides with the conclusion.
        exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46188647673122095114730032920 : ((((p4 ∧ (((p4 ∨ p3) ∨ p2) ∨ (True ∨ (((p5 ∧ p4) ∧ p5) → ((p4 ∨ p5) ∧ ((p5 ∧ p5) ∨ p1)))))) → p2) ∧ (p1 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191550307975246881637028104190 : ((p1 ∧ ((True ∧ p2) ∨ (p4 → (False ∧ (False ∨ False))))) ∨ (((p4 → ((p4 ∧ True) ∨ True)) ∧ (((p1 → p1) → False) → (p3 → p1))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p1 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68796321844383876031377458517 : ((p4 → ((((p3 → (p3 → p1)) ∨ False) → True) → ((p1 ∧ p1) ∧ (p4 ∧ (((((False ∧ True) ∨ p5) ∨ False) ∧ p1) ∨ (False ∧ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703294805651039248853668955087 : ((((p4 ∧ (((True → p4) → p3) ∨ ((p1 ∧ False) ∧ True))) ∨ ((p1 → (p1 → ((p5 ∨ (p4 ∨ p4)) ∨ ((p2 ∧ p4) → p2)))) ∨ p3)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55468101004877729821713566134 : (((((p2 → p5) → p1) ∧ (p2 → p4)) → (((False → p2) ∧ (((True ∨ (False → (False ∨ p3))) ∧ p1) ∨ (p3 → p4))) ∨ (p3 → True))) ∨ p5) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250710488338819519781228203053 : ((p1 → False) ∨ (((((p4 ∧ p3) ∨ (p1 ∨ p2)) ∨ p3) ∧ (p2 ∧ p5)) ∨ ((((p1 ∧ True) → (p3 ∧ p3)) → False) ∨ ((p1 → p3) ∨ True)))) := by
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
theorem thm_5_vars_158266420421585613336718529233 : (((p5 ∧ (p5 ∧ p5)) ∨ ((p1 ∧ (p3 → False)) ∨ (((((True ∧ True) ∨ p2) ∨ p3) ∧ False) ∧ False))) ∨ (p4 → ((p1 ∨ p5) ∨ (False → p5)))) := by
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
theorem thm_5_vars_178867930168723681709542963146 : (((p4 → (p3 → p2)) → (p4 → (p1 ∧ ((p4 → (p1 ∨ p1)) → False)))) ∨ ((p1 → False) ∨ (((p2 → (p1 ∧ p5)) ∨ (False ∨ True)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2540805163474145709261095050 : ((((p2 ∧ (p3 ∧ p4)) ∧ (p2 → p5)) ∧ p1) ∨ (((p5 → (p1 ∨ p2)) ∧ ((p2 ∨ (True ∨ (p4 ∨ p1))) → p3)) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177717946993043068374314871571 : (((((False ∧ ((p3 ∧ p3) → False)) → True) → (p1 ∧ (True → p2))) ∧ p1) ∨ (((p4 ∧ p3) ∧ ((p1 ∧ p2) ∨ (p3 → (p2 → p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626251579005142025365415842444 : ((((p3 → ((((True ∨ True) ∨ (p4 ∧ (p4 → ((True → p5) → p3)))) ∨ False) → (p5 → (p5 ∧ (True ∧ (False ∨ (False ∨ p4))))))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137535815954144742594784687318 : ((p5 ∧ (p4 ∨ (((p1 → p5) → ((p2 ∨ (p5 → (((False → p2) ∨ p5) → ((True → p5) ∨ p4)))) ∧ p4)) ∧ True))) ∨ ((p2 → True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2365805844106407920744959215 : (((((p1 ∧ (False → p5)) ∨ False) ∨ ((p5 → False) ∨ p5)) → False) ∨ (True ∨ (p2 → ((p2 → ((p3 ∨ p2) ∧ (False ∨ True))) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168690728357091882693875239501 : ((p5 ∧ (p2 ∨ ((p1 → (p2 → (p4 ∧ ((p2 → p2) ∨ ((p2 ∨ p3) ∨ p2))))) → p2))) → ((((p3 ∨ p3) ∧ p4) ∧ True) ∨ (p5 ∧ True))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47802628108610917067695514107 : ((((((False ∧ (((((True ∨ (p4 → (False ∧ p2))) → False) ∨ False) → (False ∨ p3)) ∧ p1)) ∧ p4) ∧ (p3 ∧ p3)) → True) → (p1 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_476704637435039711307147999209 : ((((p1 ∧ (p5 ∧ (((p1 ∧ p3) ∨ (p5 ∨ p4)) → p2))) ∨ (((p1 ∧ ((p5 ∧ (p2 → p5)) ∧ (p1 ∨ (False ∧ True)))) ∧ p5) ∨ True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_54271826962934374959031341279 : ((((p1 ∨ (True ∨ False)) ∧ ((p5 ∧ p3) ∧ p4)) ∧ ((False → p2) ∧ ((p1 → p4) ∨ (((((p5 ∨ p5) ∨ p5) ∨ False) ∧ p3) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50277015333074371095875863308 : (((((True ∧ p5) ∨ ((p5 ∨ ((p2 ∧ (p1 ∨ p5)) ∨ True)) ∨ ((p1 ∧ False) ∨ p3))) ∨ (p4 ∧ p4)) ∨ ((p2 ∨ p5) ∧ (p2 → True))) ∨ p2) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232113370043613588632720684077 : (((p5 ∨ p2) → False) → ((p5 ∨ p2) ∨ (p2 ∨ (p5 → ((((False ∧ (p4 ∧ ((p5 → p2) → p5))) ∧ p2) ∨ p5) ∨ (p3 ∧ (p3 ∨ p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45677295515412277897356322699 : (((p5 ∨ ((((p3 ∧ p5) ∧ (p4 → ((p3 ∧ p4) → p1))) ∧ (True ∨ p5)) → (p5 → ((True ∨ ((p5 ∨ p2) ∧ p3)) → False)))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328160056136983375333238836478 : (True → ((((p4 → (True ∨ p4)) → ((((False → ((p3 ∨ p4) ∧ p5)) ∧ (p1 ∧ p1)) ∧ p1) ∨ (p2 ∨ p2))) ∧ p5) → ((p3 → False) ∨ p5))) := by
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
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610343093588286671095204043070 : ((((((((p5 ∨ (True → True)) ∨ ((((True → p1) → (((p3 → p5) ∧ p5) → p1)) ∧ True) ∧ (p5 ∨ p2))) ∧ p4) → p1) → False) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_112112835456075605936929349929 : ((((p1 → p1) → (p5 ∨ (p2 ∨ (False ∨ (((False → (p1 ∨ (((p4 ∧ p3) ∨ p4) ∧ p4))) → (p1 ∨ False)) ∨ True))))) ∨ p3) ∨ (p1 ∨ p2)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63952752501988099670807565099 : ((False ∨ ((False ∨ ((((p3 → ((p4 ∧ ((p1 → p3) ∨ (False → (p3 → (True → False))))) ∨ (True → p5))) ∧ p2) ∧ p1) ∧ p5)) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41264361323402477249088815331 : ((((False ∧ (((p1 → True) → (((p3 ∨ p2) ∧ (p4 ∨ (p4 → (True → p1)))) ∧ p5)) → p4)) ∨ (((False ∨ p3) ∧ True) ∨ p3)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620247136647838100846867833782 : (((((p5 ∧ p2) ∨ ((p4 ∨ p3) → ((((p5 ∧ (((p1 ∨ True) → (p2 ∧ (p3 → p1))) → True)) ∧ p1) ∧ True) ∧ (p4 ∨ p5)))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_327689814900526190432935008429 : (True → (((False ∨ (((True ∨ p3) ∨ p5) ∧ ((p5 ∧ (p2 ∧ (((p1 ∧ True) ∨ ((False → False) → p2)) ∧ p5))) ∨ True))) ∨ p3) ∧ (p3 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172879484339047816957324537292 : ((p1 ∧ ((p5 → ((False ∨ p3) → (p1 ∧ False))) → (True ∧ ((p5 ∨ p4) → p5)))) ∨ (p5 ∨ (((p5 ∧ p2) ∨ p5) ∨ ((p2 ∧ p4) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734444857582110453136073016182 : ((((p1 ∨ True) ∧ ((((False → p3) ∧ ((False ∧ False) ∨ (((p5 ∨ (True ∨ p2)) ∨ ((p2 ∨ p4) → (p1 ∨ p3))) ∨ p4))) ∧ p4) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38240759044559972347281540713 : (((((p5 → (((((p3 → (p5 → (p3 → p5))) ∨ (p3 ∨ False)) ∨ p1) ∧ p3) ∨ False)) ∨ p2) ∧ (p1 → ((p1 → p5) → p5))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256580616839644477209004870639 : ((p1 ∨ True) → ((False ∨ ((((p5 ∧ p1) ∧ ((((p1 ∧ p3) ∧ (p1 ∧ p5)) → p3) → p4)) ∧ (((p3 ∧ p1) ∧ False) ∧ p3)) ∨ p3)) ∨ True)) := by
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
theorem thm_5_vars_563313311283544288442637834130 : (((p5 ∨ (((p3 ∨ p1) ∧ False) ∨ (((p5 ∧ p4) ∨ ((p1 ∧ False) ∨ (False → (False ∧ (p5 → False))))) ∨ (True ∨ ((p1 ∧ False) → p2))))) ∧ True) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343824154079697174200120557315 : (p2 → (p2 ∧ (((((p2 ∨ True) ∧ (p2 ∧ False)) ∧ (p4 ∧ p1)) ∧ p1) ∨ ((((p3 ∨ True) → False) → p3) ∧ (p5 → (p5 ∨ (p5 ∨ p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110866300703632803898909950280 : (((((((True ∨ (p4 ∧ ((p4 ∨ ((p3 ∧ (p1 ∨ False)) ∧ (False ∨ p3))) ∧ True))) ∨ (False → p5)) → p4) → True) → p4) ∧ p2) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622147891641730564582458310555 : ((((p2 ∧ ((((p5 → p3) ∧ p5) → True) → ((((p4 → (p4 ∧ ((p2 ∨ p3) → p2))) ∨ (p5 ∨ p4)) → (p2 ∧ p5)) ∧ p2))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136346563398711663530327164235 : (((p3 ∨ (False → (p5 → p2))) ∧ (True → ((((False → (p4 ∧ p5)) → p3) ∨ (p5 ∨ ((p4 ∨ False) → p3))) ∨ p5))) ∨ (True ∨ (p1 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57195553781276357089697576760 : ((((p3 ∨ p5) ∨ p4) ∨ (p4 ∨ ((p2 ∨ (((p4 ∧ (p4 → ((p3 ∧ p1) ∨ p4))) ∨ ((p3 ∨ p1) ∧ False)) ∧ p1)) → (False ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192535188100260686196123313292 : (((p1 ∧ (((False → p1) → p5) ∧ (p5 → False))) ∨ p4) → (p5 → (((p2 ∨ True) → (p5 → p2)) ∨ ((p5 ∨ (False ∧ (p2 → p4))) ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135350920399635715520192635440 : (((p5 ∧ ((p5 ∧ ((p3 ∨ p4) ∨ (p2 ∨ p4))) ∨ ((((False → p2) ∨ p1) ∧ p4) → False))) ∧ (False → (p5 ∧ p5))) ∨ (p5 → (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164526836835095401020620463421 : ((((True → (p5 ∨ (((False → ((True → p3) ∧ p5)) ∧ p3) ∨ False))) → (False ∨ p4)) ∧ p5) ∨ ((True ∨ ((p2 ∨ (p1 ∧ p4)) ∧ p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65570971971868065591207778557 : ((p3 ∨ (p4 → ((p3 ∧ (p5 ∨ (((p3 ∧ (False → (True → p2))) ∧ p1) → (False ∧ (True ∨ (p5 ∧ (p1 → (False ∨ p2)))))))) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699926395204728646304399739263 : ((((((p2 ∨ p1) ∧ ((True ∧ p2) → p1)) → ((p2 ∨ p2) ∨ p1)) → (p1 ∧ (p5 → (True → ((True ∨ p3) ∧ (False ∧ (p2 → p1))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_890735956058500338878785128477 : ((((False ∨ (p4 → ((((p5 ∨ p1) ∧ p3) → (((True → True) ∧ False) ∨ (p1 → (((p2 ∧ p3) ∨ True) ∨ False)))) ∨ p2))) → (p5 ∧ p4)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ (p4 → ((((p5 ∨ p1) ∧ p3) → (((True → True) ∧ False) ∨ (p1 → (((p2 ∧ p3) ∨ True) ∨ False)))) ∨ p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h2
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- One of the premise coincides with the conclusion.
  exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654993155503362647074367932010 : ((((((p2 ∨ p2) ∧ ((False ∨ (p4 ∨ p4)) → (p3 ∨ (((p3 ∧ (True ∧ ((False → False) ∨ True))) → p5) ∧ p1)))) → p4) ∨ (False ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350040082509676501629575048909 : (p4 → ((((p1 ∨ p1) ∨ (((p3 ∧ (((False ∨ True) ∧ p2) ∧ p1)) ∧ ((p5 ∨ ((False → p5) → p4)) ∨ (p3 → p2))) → p4)) → p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59211998331808536978965266786 : (((p1 ∨ p4) ∨ ((((p3 ∧ ((p2 ∨ p2) → (p4 → p4))) ∨ p5) ∧ p1) → (True → (((((p2 → False) ∨ p1) → p3) ∧ True) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233451648717078792851733395506 : ((False ∨ (p2 → False)) → ((p3 ∨ True) ∧ (p5 ∨ ((False ∨ ((p1 → (p5 ∧ (p1 → (p2 ∧ p2)))) ∧ ((p2 → (p4 ∧ p3)) ∨ p2))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148241657742337253688697758666 : (((((p1 ∧ ((p5 ∧ (p5 ∧ p1)) ∨ p5)) ∧ p1) → ((p4 ∧ (p4 ∧ p2)) ∨ True)) ∨ ((True → p3) ∨ p4)) ∨ ((p2 ∨ (p4 → True)) ∨ p3)) := by
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
theorem thm_5_vars_265799322623905174824590361876 : (True ∧ (p4 ∨ (p1 ∨ (((p3 ∨ True) ∧ (p1 ∨ (((((p1 ∧ (p3 → (p5 → p2))) ∨ p5) ∧ ((p4 ∧ False) ∨ p1)) ∨ p2) ∧ p5))) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_233527535712407211472741370533 : ((p1 ∨ (p1 ∨ p4)) → ((((p1 ∧ ((p2 → p2) ∨ p4)) ∧ ((p4 ∧ False) ∧ (((p5 ∨ p2) → (True ∨ p3)) ∨ p1))) ∨ (p2 ∧ True)) ∨ True)) := by
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
theorem thm_5_vars_384195261936224125812459907649 : ((((((((((True ∧ (False ∨ (p4 ∧ p3))) → p3) → (p1 ∨ p1)) ∧ (True → (p4 ∧ True))) ∧ p4) → (p3 ∨ (True → p1))) → p5) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_317800297485617280943436869401 : (p4 ∨ (((p1 ∧ (p1 ∧ (((p5 → p5) → p2) ∨ p3))) ∨ ((p4 ∧ True) → ((True ∨ ((p2 ∧ p4) → ((p2 ∧ False) ∨ p1))) ∧ p4))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67948916933135110018956389790 : ((p2 → ((((p1 → True) ∨ p1) ∧ p1) ∧ ((((False → p2) ∨ ((p4 ∧ (p3 → (True ∧ False))) ∨ p4)) ∨ p2) → ((p3 → False) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111012023564908041899753484637 : (((((((p5 → False) → p5) ∨ p2) ∨ ((p1 ∨ ((p2 → (p1 → (p2 → p4))) → p2)) ∧ p4)) ∨ ((p5 ∨ p3) → p4)) ∧ False) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299239245024801203688565304594 : (False ∨ (((((p3 ∧ ((((p2 → (p2 ∧ p3)) ∨ (False ∨ True)) ∧ False) → ((p5 → p2) ∨ p5))) → p1) ∨ p2) ∨ (False → (p2 → p2))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_49269998275616262352804553902 : (((p2 ∧ ((((p5 ∧ (p4 ∧ False)) → p3) → True) → ((p4 → (True → p2)) ∨ ((p2 ∧ (p4 ∨ p2)) ∨ p3)))) ∨ (p3 ∨ (False ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49204972661786585545329537628 : (((((True ∨ True) ∨ p4) → ((((p2 → p3) ∨ p1) ∨ p2) → ((((p1 ∧ (p1 → False)) → False) ∨ p1) ∨ p2))) ∨ (p3 → (False ∧ False))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h7
          -- Conjunctions on the left can always be decomposed.
          let h8 := h7.left
          let h9 := h7.right
          -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
          have h10 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h8
          -- We have shown the premise of h9, we can now drive its conclusion.
          let h11 := h9 h10
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h13
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
          have h16 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h14
          -- We have shown the premise of h15, we can now drive its conclusion.
          let h17 := h15 h16
          -- False on the left can always be used.
          apply False.elim h17
      case inr h18 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h19
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
        have h22 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h20
        -- We have shown the premise of h21, we can now drive its conclusion.
        let h23 := h21 h22
        -- False on the left can always be used.
        apply False.elim h23
    case inr h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h24
        case inr h27 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h24
      case inr h28 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h24
  case inr h29 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h29
      case inr h32 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h29
    case inr h33 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765000238269512321216299874162 : (((p4 ∧ ((p5 ∨ (((p3 → ((p5 ∨ p3) → ((p2 ∨ p4) → (p1 ∨ p1)))) ∧ (((False → p4) → p3) ∨ (False ∧ p5))) → p4)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61528573165484331732555019024 : ((p1 ∧ ((((p5 ∨ (p1 → (p4 ∧ (p5 ∨ (True ∧ True))))) → p1) → (True → p2)) ∨ ((False ∧ (p2 → p4)) ∨ ((p1 ∨ p5) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350914725471800410721703118874 : (p4 → ((((False ∧ (p1 → (p3 ∨ (((((p3 ∨ p4) ∨ (p3 ∧ p5)) ∨ (p2 ∨ (p1 ∨ p3))) → True) ∨ False)))) ∧ p1) ∨ p1) ∨ (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186317002559239462653739115724 : ((((p3 → ((p4 ∧ (p4 ∨ p4)) ∨ p4)) ∨ (p5 ∨ p2)) → False) → ((((True ∨ True) ∧ (p5 ∨ p5)) → p2) ∨ (p3 → ((True ∧ p1) ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h7 : ((p3 → ((p4 ∧ (p4 ∨ p4)) ∨ p4)) ∨ (p5 ∨ p2)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h8 := h1 h7
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h10 : ((p3 → ((p4 ∧ (p4 ∨ p4)) ∨ p4)) ∨ (p5 ∨ p2)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h11 := h1 h10
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h13 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h14 : ((p3 → ((p4 ∧ (p4 ∨ p4)) ∨ p4)) ∨ (p5 ∨ p2)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h15 := h1 h14
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h17 : ((p3 → ((p4 ∧ (p4 ∨ p4)) ∨ p4)) ∨ (p5 ∨ p2)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h18 := h1 h17
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342199440167174522488872514484 : (p2 → (((p4 → (((p2 → ((p3 ∨ p2) → (p1 ∨ p4))) ∧ ((p5 → p1) ∧ p5)) ∨ p5)) ∧ (p2 → p1)) → ((False ∨ (p1 ∧ p1)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h6
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314735805830288353563781843451 : (p3 ∨ ((((((p3 → p5) → (p2 ∧ ((p1 → p2) ∧ p5))) ∧ p5) ∧ p3) ∨ p2) ∨ (((p4 ∧ p2) → p4) ∨ (p4 → (True ∨ (p1 ∨ False)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601384934985453864548455053468 : ((((p2 ∧ (False ∨ (((False ∧ p5) → ((p2 → ((p1 ∨ p3) ∧ (False → p2))) → (p1 → p1))) ∧ (((p5 ∧ False) ∧ True) ∧ False)))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346296194233125113585470941284 : (p3 → ((((True ∧ (p1 → (((False ∧ (True ∨ p5)) ∧ p5) → p4))) ∧ (p1 ∧ (((False ∨ p5) ∨ (p2 ∧ p5)) ∨ p2))) ∨ True) ∨ (p5 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350822745682824541822740853754 : (p4 → (((((p1 ∧ True) ∧ (p3 ∨ False)) ∧ (((p4 → p4) ∨ p2) ∧ ((p2 → p3) ∧ (p4 ∨ (p1 ∧ p2))))) ∨ (p1 ∨ p4)) ∧ (False → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115137699922564032524457394650 : ((((p2 → p3) ∨ (((((True ∧ p3) ∨ p1) ∧ False) → False) ∧ p2)) → (((p3 ∨ (p3 ∨ p2)) → (p4 ∨ (p2 ∧ p3))) ∨ p1)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316583531446028027377628746009 : (p3 ∨ (p3 ∨ ((p3 ∧ p3) → ((((True ∧ p5) ∨ (p1 → ((False → ((False ∧ p3) ∨ p2)) ∨ p3))) → (False ∧ p5)) ∨ (p2 → (p3 → p2)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48389307234196353731341881713 : (((False → (((p1 ∨ ((((p1 → True) ∧ True) ∨ ((p2 ∨ p5) ∨ (p1 ∧ (p1 ∧ True)))) → p1)) → (p4 ∧ p1)) → p3)) → (False ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138746124022752356240673820617 : (((((p4 → False) → p4) ∧ (False ∨ ((p1 → (p3 ∧ (p2 ∧ ((p5 → p1) → False)))) → ((p3 ∨ False) ∨ False)))) ∧ True) → (p3 ∨ (True ∨ p3))) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115308860826569573975899773960 : (((((p3 ∨ (p4 → True)) → (p3 → p3)) ∨ (p1 ∧ p1)) → (((p4 → True) ∨ p3) ∧ ((p5 ∨ ((p2 ∧ p2) ∨ True)) ∨ False))) ∨ (p1 → False)) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136037356855765013798528118240 : (((p2 ∧ (((((False ∨ p1) ∨ p5) → p3) ∨ p5) ∧ p4)) → (((True → p1) ∧ ((p4 ∨ (p5 ∧ p3)) ∨ False)) ∨ p4)) ∨ ((p3 ∨ p4) ∧ p3)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204587727566499233980608028877 : ((((p5 ∧ False) ∨ (p2 → p1)) ∨ p5) ∨ (p5 ∨ ((p1 ∧ (p5 → ((p4 ∧ p2) ∧ p1))) → (p3 ∨ (False → (p1 ∨ (p2 ∨ (False ∧ p5)))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226335722639526983484054566933 : (((p5 ∨ p3) ∨ p4) ∨ (((((p5 ∧ True) ∧ (p5 ∧ True)) ∧ ((p2 ∨ p3) ∨ (True ∨ False))) ∨ (((p1 ∧ p1) ∨ p4) ∨ True)) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229920749309962300250907623602 : ((p5 → (p4 → p1)) ∨ ((p5 ∨ (((True → (p1 ∧ (p5 ∨ (True ∧ True)))) → ((((p5 → p3) ∧ p5) ∧ p2) ∧ (p1 ∧ p5))) ∨ True)) ∨ False)) := by
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
theorem thm_5_vars_191571244771734049331389529193 : ((p2 ∧ (((p4 ∨ (False → (p4 → p1))) ∧ p1) → False)) ∨ ((True ∧ (True → ((p1 ∧ p1) → ((p2 → True) ∨ p4)))) ∧ (False → (p5 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143795006999707963232225237858 : ((((((((p3 ∧ p2) ∨ True) ∨ p3) → ((True ∨ (((p2 → p1) → p5) → True)) ∨ p4)) → p1) ∨ p5) ∨ True) ∧ ((p4 → (False → p1)) ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54339575572447604340233666264 : (((p5 ∧ (p4 ∧ ((False → (False ∧ p4)) ∧ p3))) ∧ (((p3 ∧ p4) → (((p1 → ((p2 → p5) ∧ p3)) → (p5 → False)) ∧ False)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68519859096485009000590458928 : ((p3 → (True → ((p1 → (p2 ∨ (False ∧ (((p1 → (p4 → p1)) → (p2 ∧ (p1 ∧ (p3 → p1)))) ∧ p3)))) ∨ (p4 → (p3 ∧ p4))))) ∨ p5) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717327777796646604584884967695 : ((((p5 ∨ ((p3 ∨ p2) ∨ True)) ∧ ((p4 → ((p2 → (p5 ∧ (p3 → p5))) ∧ (((p5 → p3) ∨ (True → (p1 ∨ p3))) ∨ p5))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347975687842840260990851625911 : (p3 → ((p2 → True) ∧ ((p4 → ((False → ((((p5 ∧ True) → True) ∧ p4) → True)) → (((((False → p3) → True) → p5) ∨ p2) ∧ True))) ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639583715814420060403631924474 : ((((((p3 ∨ p3) → p3) ∧ (((((False → False) ∧ p5) → (p4 ∧ False)) ∧ ((((p5 ∧ (p4 → False)) ∧ False) → True) ∧ p2)) ∨ True)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84014846384376409708985484988 : ((((((False ∧ (p2 ∧ p1)) ∨ ((p5 → ((p1 ∨ True) ∨ p4)) ∨ True)) ∧ p5) → False) ∧ ((p1 ∨ (p5 → ((p4 ∧ p2) ∨ p3))) → False)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p1 ∨ (p5 → ((p4 ∧ p2) ∨ p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : (((False ∧ (p2 ∧ p1)) ∨ ((p5 → ((p1 ∨ True) ∨ p4)) ∨ True)) ∧ p5) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h4
  -- False on the left can always be used.
  apply False.elim h8



