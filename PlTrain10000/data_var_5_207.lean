variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346253809730880059731975421883 : (p3 → ((p3 ∧ ((((p3 ∧ (p5 ∧ (p1 ∨ ((False ∨ p3) ∧ False)))) → True) ∨ (p1 ∨ False)) → ((p3 → (p1 ∧ False)) → p2))) ∧ (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h10 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h11 := h3 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207639815066965111669347563670 : ((((p4 ∧ p5) ∧ (p3 ∨ p3)) → p5) → (((p1 → (p3 → p4)) ∧ False) ∨ (p1 → (((True ∧ ((False ∧ (p2 ∧ False)) ∨ False)) → True) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41254109831772961210037433644 : ((((((p4 ∧ ((True ∨ (False ∧ p4)) → True)) ∧ (p1 → (p3 ∧ p4))) ∨ (p1 ∨ (False ∧ p3))) ∨ ((False → (p4 ∨ p5)) → p1)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733609604298142053247862677280 : ((((p4 ∧ p5) ∧ (p3 ∧ (p1 → (((p5 → p1) ∨ ((p3 → (p4 → p2)) ∨ (p2 ∨ p4))) → ((p1 ∨ p4) ∧ ((False ∨ p1) → p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60414612882246108066065048172 : (((p4 → p1) → ((p3 → (False ∧ (((p5 → (((p1 ∧ (p2 → p4)) ∧ p5) ∨ p3)) ∧ p1) ∧ (p5 → p5)))) ∧ (False ∧ (p2 → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44437934344656862273698999467 : ((((p2 ∧ (((True ∧ True) ∨ p5) → ((p4 ∧ p1) ∨ (p5 → p1)))) ∧ (((p1 → (((p4 ∧ p5) → p4) ∧ p1)) → True) ∨ p5)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172322983944123495385423341499 : ((((p2 ∨ ((p5 → p4) → p1)) ∧ p5) ∧ (False ∧ (p5 → ((p4 → p3) → p1)))) ∨ ((((p4 ∧ p2) ∨ (p5 ∨ p1)) → p1) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186931160557492540962035079677 : (((p1 ∨ (p2 ∧ p1)) ∧ ((p1 → ((p3 → p1) ∨ p2)) → p1)) → (((p3 → (p4 ∧ False)) ∨ (((p5 ∨ True) → (p5 → p1)) → p5)) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57093721640107393542622163735 : ((((p4 ∧ False) ∧ p4) ∨ ((p2 ∧ False) ∨ ((p3 ∧ (True ∧ p4)) ∨ ((((p1 → ((p4 → False) ∨ False)) ∧ p2) ∨ p1) → (p1 ∨ p2))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_475974085993541603116922468342 : ((((((((p3 ∧ (p2 ∨ p3)) ∧ p2) → p5) ∨ p3) → p5) ∨ (((True → p1) ∧ (p2 ∧ (p2 → ((p3 ∨ True) ∧ False)))) → (p2 → p4))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244575639525942875507930361901 : ((False ∧ p4) ∨ (((False ∨ False) ∨ (False ∨ ((((p3 ∧ p1) ∧ p1) ∧ p2) ∧ p4))) ∨ ((((False ∨ (p3 ∧ p3)) ∧ (p3 ∧ p2)) ∧ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174730980058389546699832958900 : ((((p3 → True) ∨ p3) → (((((p5 ∧ False) ∨ p4) ∧ False) → p5) ∧ (p3 ∨ False))) → ((p3 ∨ p3) ∨ (((p1 ∨ p1) → p4) → (p5 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 → True) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_93073279032957805669891536401 : ((True ∧ (((p5 → (p1 → (p3 → p1))) ∨ False) ∧ ((((p1 → True) → (((p5 → p5) ∨ True) ∧ (p4 ∧ False))) ∧ (p5 ∨ p4)) ∧ True))) → p3) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h12 : (p1 → True) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h14 := h9 h12
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h18 : (p1 → True) := by
        -- Implications on the right can always be decomposed.
        intro h19
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h20 := h9 h18
      -- We need to get the right conjuct of h20 based on <expert-advice>.
      let h21 := h20.right
      -- We need to get the right conjuct of h21 based on <expert-advice>.
      let h22 := h21.right
      -- False on the left can always be used.
      apply False.elim h22
  case inr h23 =>
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233704036039612166957339847912 : ((p2 ∨ (p5 → True)) → (p1 ∨ (((p1 → (True ∨ ((p2 ∧ False) → False))) ∧ ((p1 → (True → (p5 ∨ p3))) → ((p1 → p2) ∧ p3))) ∨ True))) := by
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
theorem thm_5_vars_357087990327016273584808962056 : (p5 → (((p3 ∨ p2) → p2) → ((p2 ∧ (False ∨ (p3 ∧ ((((True → p1) → p1) ∨ (True ∧ p4)) ∨ p1)))) ∨ (((p2 ∨ p2) ∨ p5) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354597313042811455647056434044 : (p5 → (((((p3 ∧ (False ∨ ((p3 → p2) ∧ ((((p3 ∨ p5) ∧ ((p5 ∧ (True → p2)) ∨ False)) ∨ True) ∧ p3)))) ∧ p4) ∧ True) ∨ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306548004065056288398888418071 : (p1 ∨ ((p5 ∧ p5) → (p1 → ((p2 ∨ ((p1 ∧ ((False ∨ ((False ∨ (p1 ∨ False)) ∧ p4)) ∨ False)) ∨ ((False ∧ True) ∨ p3))) ∨ (p5 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249862579969633901359870043850 : ((True → False) ∨ (((True ∨ (p3 ∨ p1)) ∨ (p4 → False)) ∧ ((((((p1 ∧ p3) → p1) ∧ True) → p5) ∧ ((p1 → p4) ∧ (p5 → True))) → p5))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (((p1 ∧ p3) → p1) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h6
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786994161086675789523664650843 : (((p4 ∨ ((p3 ∨ p5) ∧ (False ∨ ((((p1 ∧ ((False → (p2 ∨ p2)) ∨ p2)) ∧ (((p1 → p5) → (p5 ∨ True)) → False)) ∧ p2) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117306317580439213262824057346 : ((False ∧ (((((p4 → p5) ∧ ((p5 ∨ (False ∨ (p2 ∧ p1))) ∨ False)) ∧ True) → (True ∧ (p3 ∨ False))) ∨ ((False ∨ p3) → False))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625059183313552835312047754584 : ((((True → (((p1 ∨ p5) ∧ ((((True → (((p5 ∨ True) → p4) → (True ∧ False))) ∨ (p5 → p5)) ∧ (p2 ∨ True)) ∨ True)) ∨ p1)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_168152558291312931792665475014 : ((((False → p2) ∧ p3) ∧ (p4 ∨ (((p2 → True) → (p4 → p5)) ∧ (p4 ∨ (p4 → p2))))) → (p2 → (p2 ∨ ((p1 → (p3 ∨ p4)) ∨ True)))) := by
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
  cases h4
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40262700365770468990603005527 : ((((p3 ∨ (((p2 ∨ True) ∧ False) ∨ (((False → (p5 ∨ p2)) ∨ False) → ((True → True) ∨ ((p4 → (p4 → p4)) ∧ True))))) ∧ False) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623949143981269932064187854115 : ((((p2 ∨ ((((((p1 → True) ∧ ((p4 ∧ (True ∧ True)) → (p2 ∧ (p3 ∨ (p2 ∨ p2))))) ∧ p1) → False) → (True → p1)) ∨ p4)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592255757705140589726273432041 : (((((((((True ∧ p3) ∨ p4) ∧ (p4 ∧ (((p1 ∧ (p3 ∨ p5)) → p5) ∨ ((p4 ∨ False) ∨ True)))) ∧ p2) → True) → (p5 → False)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60655043513959140466545613137 : ((True ∧ (((p4 ∧ (False ∨ (((p5 → (p3 ∧ True)) → (False ∨ ((False ∧ p5) ∧ p1))) ∧ True))) ∨ p5) ∨ (False → (p4 ∧ (p1 ∧ True))))) ∨ p2) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705231443729345811078164154707 : (((((p1 ∧ ((p5 ∨ p1) ∨ (False → p1))) ∧ True) ∧ (((p4 ∧ (True → (p1 ∧ p2))) ∧ True) ∨ ((p4 → (p1 ∧ p5)) ∧ (p5 ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135007034700849838086702965985 : (((False ∨ ((((((True ∨ p2) ∧ False) ∧ (False ∨ (p2 ∧ p5))) → p4) → p1) ∨ (True → (False → p3)))) ∧ (True ∨ p5)) ∨ ((p4 → p2) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204107333048282810913461090855 : (((((p1 → p3) ∧ p4) ∧ p1) ∧ p3) ∨ ((True → (p4 ∧ p5)) ∨ (p5 → (((p3 ∧ True) ∧ ((p4 → (False ∧ p1)) → True)) → (p4 ∨ p3))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658470803068790875435542937569 : ((((p1 ∨ (((p4 ∨ p1) → p5) → ((p3 ∧ p1) → (((p5 → True) → ((p1 ∨ (p3 → (False ∧ p2))) ∧ p2)) ∨ True)))) ∨ (False ∧ p1)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683739107166307714369401840566 : (((((((((p2 ∧ p5) ∨ (p5 ∨ p5)) ∧ False) ∧ (p2 ∨ (p3 ∨ (p5 ∧ p2)))) ∧ False) ∨ False) ∨ (((p5 ∧ p4) ∧ (False ∨ False)) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115448815853319341969491137642 : ((((False ∧ (p1 ∨ p2)) ∨ (True → (False ∧ p2))) ∨ (True ∨ (p5 ∧ (p4 → (True ∧ (p1 → ((p2 ∨ (p2 → False)) ∧ False))))))) ∨ (p1 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669445709547793512904961861925 : (((((p4 ∧ ((((True → p5) ∧ (p3 → False)) ∧ ((False → False) ∧ ((False ∧ False) ∧ p1))) ∨ p3)) ∨ (p2 ∨ p3)) ∨ (p4 ∨ (p4 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51237292694766042418119494618 : ((((p2 ∧ (p1 ∨ p4)) ∧ (((p2 ∨ (True ∧ p1)) → (((p5 ∨ p3) → p3) → p2)) ∧ p1)) ∨ (False → (((p3 ∧ True) ∧ p3) ∨ p3))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147085061984980392147468515033 : (((((True → (p2 → p2)) → p4) ∨ (p5 ∧ ((((False ∨ p5) → p3) ∨ p5) → ((p3 ∨ p3) → p3)))) ∧ p1) ∨ (False → (p5 ∧ (True ∨ True)))) := by
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
theorem thm_5_vars_52626009437689429773310691891 : ((((p2 ∨ (p3 → False)) → (((True ∧ (p1 → True)) → p2) ∨ (False ∨ True))) ∨ ((((True ∨ True) ∨ p2) ∨ p4) ∧ (p5 ∨ (True ∨ p2)))) ∨ p2) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320124795243256290605399576663 : (p4 ∨ ((p2 ∨ (p5 ∧ True)) → (((False ∨ p1) ∧ ((p4 ∧ p1) → (((((True ∧ p5) → p5) ∧ ((p5 ∧ p3) ∧ False)) ∧ True) → p1))) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54714387480274721690530566195 : (((((p4 → (True → True)) ∨ p5) → (p4 ∧ False)) → ((((p3 ∧ p5) ∨ True) ∧ ((p4 ∨ p1) ∨ p4)) ∨ (p5 → ((p1 → p5) ∨ True)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_244276088405322483492969067458 : ((False ∧ True) ∨ ((p1 ∧ ((p2 ∧ (True ∨ p5)) ∧ p3)) ∨ ((p1 → (p5 ∨ (p3 → p1))) ∨ (p4 → (p2 → (p3 ∧ ((p1 ∧ True) ∧ p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119069098775781505114627608230 : ((p1 → (((p5 ∧ ((p3 → ((True → p5) ∨ (True ∧ (p5 → p3)))) → ((True → p2) → (p5 → False)))) ∧ p4) ∨ (False ∨ True))) ∨ (p5 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329272388981446213743817186764 : (True → (((p3 ∨ False) ∨ False) ∨ ((p2 ∨ p3) ∨ ((p2 ∧ (((True ∨ ((False → p3) → p2)) ∨ (p2 ∨ p2)) ∧ ((p2 → p2) ∧ p2))) → p2)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h6.left
      let h10 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h6.left
      let h13 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h6.left
      let h17 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h6.left
      let h20 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64991288922065806962980060155 : ((p2 ∨ ((p4 ∨ (False ∨ False)) ∧ ((((((p2 → False) ∨ (p5 ∨ (p4 ∨ False))) → True) → (True → (p3 ∧ (p5 ∨ False)))) ∨ p2) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759126502365054950221133051062 : (((p2 ∧ (((False ∧ False) ∧ (((False ∧ (p5 ∧ p5)) → ((p3 ∨ (p4 ∨ True)) ∧ (p2 ∨ True))) → (p4 ∨ (p5 ∨ True)))) ∧ (p1 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185091581817219011950877305311 : (((p4 ∨ p2) ∨ ((False ∨ (((True ∧ p5) → False) ∨ p2)) → p4)) ∨ (False → ((p3 ∧ (((p3 ∨ p2) ∧ (False ∧ p1)) ∨ p5)) → (p4 ∧ True)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h7.left
      let h13 := h7.right
      -- False on the left can always be used.
      apply False.elim h12
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80834281368072623574117800655 : ((((((p5 ∨ (p5 ∨ ((p5 ∧ p5) ∨ p4))) → (True → p5)) ∧ ((True ∧ ((p5 ∧ True) ∧ p1)) ∨ p4)) ∧ p2) ∧ ((True ∧ p3) → p3)) → p5) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h15 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h16 : (p5 ∨ (p5 ∨ ((p5 ∧ p5) ∨ p4))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h17 := h6 h16
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h18 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h19 := h17 h18
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312371626277615280049630657404 : (p2 ∨ (p3 → (((p1 → (p3 ∧ (p1 ∨ ((True ∨ p3) ∨ ((False ∨ True) → p3))))) ∧ p5) → ((p2 → (p3 → ((True ∨ False) → p1))) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347509123713469452881154951037 : (p3 → (((((p4 ∨ True) ∧ p5) ∨ True) ∨ True) → (((False ∨ (False → p1)) → (((p5 → p4) ∨ p2) → (p3 → (p1 ∨ p2)))) ∨ (p3 ∨ p3)))) := by
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
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55200853479777585381797013193 : (((((p2 ∧ False) ∧ False) ∧ (p4 ∧ False)) ∨ (((p1 ∧ (p1 → (p4 ∨ (True → False)))) ∨ ((False ∧ p3) ∧ ((p2 ∨ p5) ∨ False))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179657831898732744985853359185 : ((p5 → ((p4 ∧ ((p1 ∨ p4) ∧ p5)) ∨ (((p3 ∨ True) → True) ∧ p2))) ∨ ((p5 ∧ (p3 → (p3 ∨ (p1 ∧ True)))) ∨ (p4 → (p5 → p5)))) := by
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
theorem thm_5_vars_219947035538920224585227001480 : ((p5 → ((p2 ∧ p5) ∧ p5)) → (True → ((False ∨ (((((True ∧ False) ∨ p3) ∧ p5) ∧ (p4 ∧ (((p3 ∧ True) → p1) ∨ p5))) ∨ True)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40497927210807870848411104451 : ((((True ∧ ((p2 → (False → p3)) → (((p3 ∧ p5) ∧ (p5 → p2)) ∧ ((p5 → (((p4 → p1) ∧ False) ∧ True)) ∨ False)))) ∨ p2) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171515935894108785927937294515 : (((((p5 ∨ p5) ∨ (((p2 ∨ p5) ∧ (True ∧ (p1 ∨ False))) ∧ p3)) ∧ p4) ∨ p2) ∨ ((p1 → ((p2 ∧ (p2 → (True → p2))) ∨ True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185707805521062545691898910307 : ((p2 → (((p4 → (True → False)) → (p1 ∧ p2)) → (False ∧ p4))) ∨ ((p1 ∧ (p2 ∧ (((p3 ∧ ((p1 → p2) → p1)) ∨ p3) ∧ p3))) → p2)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43462914879568469477073047628 : (((((p2 → p3) ∨ ((p5 → ((p5 ∧ (p3 ∧ ((p2 → p1) ∨ p4))) ∧ (p4 → p5))) ∨ (p3 → ((True → p4) ∧ p4)))) ∨ p4) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58513915984953367117381772458 : (((p5 ∨ True) ∧ ((p5 → ((False → p1) → ((p4 ∨ ((False → p3) ∨ ((p2 ∧ (p4 ∨ p2)) ∨ (p4 ∧ p3)))) → p5))) → (p2 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51092774353444961731218056090 : (((((((p5 ∨ ((p4 → True) ∨ (p5 ∨ (p2 ∨ p3)))) ∨ p5) → p4) ∨ (True ∧ p4)) ∧ p4) ∨ ((p1 → p1) ∧ (p2 → (False → p2)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238257186686707742058093933570 : ((True ∨ p5) ∧ ((((p1 ∧ (((p3 ∨ True) ∨ p1) ∨ ((p3 → p5) → p3))) ∧ (p3 → p4)) ∧ True) → (False ∨ (((p2 ∨ p1) ∨ True) ∨ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322198943972770508777185804255 : (p5 ∨ (((((p4 ∨ True) → ((((((p5 → ((p5 ∧ p3) ∧ p3)) ∧ p4) ∧ p2) ∨ (p2 ∨ p5)) ∧ p4) ∨ (p4 → False))) ∧ p2) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346297672405232311200802078194 : (p3 → ((((False ∧ (True ∧ p1)) ∨ ((((p2 ∨ p5) ∧ (((p4 → p2) ∧ ((True → p1) → p5)) ∨ p1)) ∨ p3) → p5)) ∨ True) ∨ (p3 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345261849134351506372750835412 : (p3 → ((p4 ∨ (((p2 → True) ∧ (((p2 ∧ True) ∧ ((p2 ∨ p1) ∧ ((p2 ∧ True) → (p2 → (p5 ∨ (p2 ∨ p5)))))) → p5)) ∨ True)) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309662060311059086886177678063 : (p2 ∨ ((p3 → (p5 ∨ (((((p5 → False) ∨ (p4 → False)) ∧ (False ∨ (p2 → (False ∧ (p5 ∧ True))))) → p3) ∧ p4))) ∨ (p1 → (False ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750432690791436421228461934219 : (((True ∧ (((p1 ∨ (((True → True) → (((p4 → p3) ∧ p1) ∨ (p2 → ((p1 ∧ p1) ∧ p5)))) → p4)) ∨ True) ∨ ((p4 → True) ∨ p1))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1810303891714526409182751763 : ((p5 ∧ ((p3 ∧ (p3 ∧ ((((True → p2) → ((True ∨ (p2 → False)) → p5)) ∨ True) ∨ p5))) ∧ (True ∧ p1))) ∨ (p3 → (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148066186755889372478975569164 : (((p3 → (True → (((p1 → p1) → (p1 ∧ p5)) ∧ (((p2 ∧ p2) ∨ (p2 ∨ False)) ∧ p5)))) ∨ (p4 → True)) ∨ ((p4 ∨ p3) → (False ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148387600304613968717875117395 : ((((p2 ∨ (p5 → p1)) ∨ (p3 ∨ (p3 ∧ ((p1 ∧ (p2 → p3)) ∧ p3)))) ∨ ((p2 ∧ (p1 → p4)) → True)) ∨ ((True → p4) ∨ (False ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42877329227317218858482689307 : (((p2 → (p2 → (((p2 → p5) ∨ ((((p3 → p5) ∧ ((((p4 ∨ p2) ∧ (False ∨ p1)) → p4) ∨ True)) → False) ∧ p5)) ∨ p2))) ∨ p3) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175298433885578542198670297088 : ((p3 ∨ (False ∧ ((((p1 ∧ p1) ∨ p5) ∨ p1) ∨ (p3 ∧ (False → (False ∧ p3)))))) → (((p1 ∨ p1) → (p2 ∨ p4)) ∨ ((p5 → p4) ∨ p3))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178329984073674958337398532674 : ((((p4 ∨ ((p4 ∧ p1) → p5)) ∧ ((p4 → False) ∨ p5)) ∨ (p3 ∨ p4)) ∨ ((((((p4 ∧ False) → p1) ∨ p3) ∨ p4) → p2) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_866318355199334804974140049130 : ((((((p4 ∨ p1) ∧ p5) ∨ (((p2 → (p2 ∧ p4)) ∨ (p4 → (((p2 ∧ (((False ∧ p1) → p2) ∧ p4)) ∨ p2) ∧ p3))) ∨ True)) → p4) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 ∨ p1) ∧ p5) ∨ (((p2 → (p2 ∧ p4)) ∨ (p4 → (((p2 ∧ (((False ∧ p1) → p2) ∧ p4)) ∨ p2) ∧ p3))) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306008056200153375746040090317 : (p1 ∨ (((p1 → p2) → (p4 ∧ p3)) ∨ (True ∨ ((p3 ∧ (((((p3 → (True ∧ p4)) → True) ∨ True) → p2) → p2)) ∨ (p2 ∧ (p2 → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350138529025326385418720138722 : (p4 → (((((((p5 ∧ p2) ∧ ((p4 ∨ p5) → p3)) ∧ p1) ∨ p2) ∨ False) ∧ ((p5 ∧ (p3 ∨ p4)) → (p1 → (p1 → (p5 ∨ True))))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670845047058721589851199676301 : ((((p2 ∧ (((p5 ∧ (p3 ∨ (True ∨ (p1 ∧ (p1 ∨ (((True ∧ False) → p1) ∨ p5)))))) ∨ True) → (p4 ∨ True))) ∨ (p3 → (True → True))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_114370720873639668249693442236 : (((((p5 → False) ∧ (((False ∧ False) ∧ ((p5 → p5) ∧ (p5 ∨ (True ∧ p5)))) ∨ p5)) ∨ False) ∨ ((p3 ∨ (False ∧ p4)) → p3)) ∨ (p3 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329100460650944494909647001613 : (True → (((p1 ∨ (p3 ∨ False)) ∧ True) ∨ (p2 → ((p1 ∧ p3) ∨ (((False → False) ∨ (p1 ∨ (False → (((p3 ∨ True) → p1) ∧ p1)))) ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42308411166803462639628004840 : (((p2 ∧ ((p5 ∨ (p5 ∧ ((p1 ∨ (p4 ∨ (False → p3))) ∨ p3))) ∧ ((p2 → p5) ∨ ((True ∨ (p3 ∧ p2)) ∨ (p5 → p2))))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114488112130247289017520225339 : (((((((p3 → p5) → (False ∨ (p3 → p4))) ∨ False) → (p3 ∧ p3)) → (False ∨ (p4 ∧ p4))) → ((p1 ∨ (True ∧ p2)) ∨ p2)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196692440781434925723597889202 : (((((p3 → p2) ∨ (p4 → p2)) ∨ p2) ∧ p3) ∨ (((p5 ∨ (((True ∧ True) ∨ p5) → p1)) → ((p1 → p2) ∨ (p1 ∨ p4))) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8094422985659377871134940267 : (((((((p2 ∨ p1) ∧ p2) ∨ p2) ∨ ((p4 ∧ True) ∧ (((True ∧ (False ∨ (p1 → ((True → False) ∧ p2)))) ∧ p5) ∧ p5))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799646444059387096819137804747 : (((p1 → (True → ((False → (((p2 ∧ p2) → ((((p3 → (p2 ∨ (p4 ∨ p5))) ∧ p2) ∨ p1) → p3)) → (False ∨ (p1 → True)))) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174074212986787389116050456322 : (((((((True ∨ p1) ∧ p1) → False) → (True → (p5 → False))) ∨ p3) ∧ (p5 ∨ False)) → (p1 ∨ (True → (((p4 ∧ False) ∧ (p2 ∧ p3)) ∨ p5)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749531167490497991053631786659 : (((True ∧ ((p1 ∧ ((p4 ∧ (True ∨ (False → (p4 → p1)))) → (p3 ∨ (p3 ∧ ((((p4 ∧ True) → p4) → (True ∨ True)) ∧ p4))))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57652073795744390598391191140 : ((((p2 ∨ False) ∨ p3) → (p2 ∨ ((((((((p2 → True) ∨ True) ∧ p2) ∨ ((p4 ∨ False) ∧ p2)) ∧ (False ∨ p5)) → p1) → p2) ∨ p3))) ∨ p4) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251378791491234874902769267992 : ((p2 → p4) ∨ ((p4 → ((((True → p5) ∨ (p5 ∨ p3)) ∧ p1) ∧ p1)) ∨ (p4 → ((False → p3) ∧ (p4 ∨ (True ∨ (p1 ∨ (False → p1)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_157354847657283612685571307934 : (((False → (((((p1 → p5) ∧ (p5 → ((p2 ∨ p2) ∨ p3))) ∨ p5) ∧ (p4 ∨ p5)) ∧ p5)) → p1) ∨ (p1 → (((p2 ∧ p4) ∧ p4) → p1))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683187848095986235544562749792 : ((((p5 ∧ (((p1 → p2) ∨ (((p1 → p2) → p1) ∧ p2)) → (((p4 ∨ True) ∨ p1) → False))) ∧ ((False ∧ False) ∧ ((p1 → p2) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111211839906162405623415605590 : ((((p1 → (p5 ∨ p3)) ∨ (p3 ∨ ((p3 → (((p4 → p1) ∨ p4) ∨ False)) ∨ (((p4 ∨ p4) ∧ False) ∧ (p2 ∨ p3))))) ∧ p5) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59632744975594350080885807855 : (((p5 → p2) ∨ ((p1 ∨ (((p5 ∨ (((True ∨ False) ∨ (p1 ∧ p3)) ∧ (p4 ∧ (p3 ∨ p3)))) ∧ (p3 ∧ True)) ∨ p5)) ∨ (False → False))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765800340728892721512565912362 : (((p4 ∧ ((((p5 ∨ ((False ∨ p4) → p2)) ∧ p1) ∨ p1) → ((((p1 → ((p5 ∧ (p4 ∧ p5)) → p1)) ∧ (p3 → True)) ∧ p2) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649687838123744346704055184 : (((True → ((((True ∨ False) → False) ∨ ((True ∨ p3) ∧ (True ∧ (p3 → (p4 ∨ (p1 ∨ p1)))))) → p1)) ∨ (True ∨ (False ∨ p5))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624673265741617143189983188918 : ((((p4 ∨ (p1 ∧ ((p1 ∨ (((p5 ∨ (p2 ∨ p1)) ∧ (p2 ∨ True)) ∨ p5)) → ((((p4 ∨ p2) ∨ True) ∨ (False ∧ p5)) ∧ p1)))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116817641552867336678016447485 : (((p4 ∨ p2) ∨ (((p2 ∧ p1) ∧ ((p2 → (((p3 ∧ True) ∧ ((p4 ∨ False) ∨ p4)) ∧ (p1 ∨ (p3 → False)))) ∧ p3)) ∨ True)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809349270128688940705542868779 : (((p5 → ((p2 ∨ (((((p4 ∧ p3) → (True ∧ ((True ∧ (p1 ∧ ((p4 ∨ p4) ∧ False))) ∨ p3))) → p1) → (p2 ∨ p2)) ∧ p5)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58762264554647605227804997168 : (((p4 → p1) ∧ (((p4 ∧ p5) ∨ ((p1 → p5) ∧ (p1 → p2))) ∨ ((((((True → False) ∧ (p2 ∧ True)) ∨ p1) ∧ p1) → p1) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41708835644520281685729400447 : ((((p5 ∧ ((p4 ∧ (True → True)) → True)) → ((p3 → p1) ∧ ((p4 → True) ∧ ((p1 ∧ p5) ∨ ((p3 ∨ (p3 ∨ True)) ∨ p3))))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736935080064489304203636603102 : ((((p3 → True) ∧ ((p5 ∨ ((p3 ∨ (((p5 ∨ p1) ∨ False) ∨ p3)) → (((p3 → (True ∧ p2)) ∧ True) ∧ (p3 ∧ (p3 → p3))))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58386235910045897801243627394 : (((p1 ∨ p4) ∧ ((p1 ∨ p2) ∧ ((((((p5 ∧ p2) → p4) → p1) → (((((True ∨ p5) → p3) → p1) ∨ p4) ∧ True)) → p4) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138051998776972595815113638835 : ((True → ((p2 → False) ∨ (((p1 ∧ (p2 ∨ (((True ∧ False) ∧ p2) ∨ True))) ∧ p1) ∨ ((False ∨ p4) ∨ (p5 ∨ True))))) ∨ ((p5 ∧ p4) → p5)) := by
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
theorem thm_5_vars_174689692593954236471484438567 : ((((p1 ∨ p5) ∨ p2) ∨ (((p4 → (p5 → ((p1 ∧ True) ∧ p3))) ∨ p3) ∨ True)) → ((False ∨ ((True ∨ p1) ∨ p3)) ∨ (p5 → (p4 → False)))) := by
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
      case inr h5 =>
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
    case inr h6 =>
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
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
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
      case inr h10 =>
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
    case inr h11 =>
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
theorem thm_5_vars_137030922706985720390796848601 : (((p4 ∨ p5) → (p3 ∨ (p1 ∧ (((p1 ∧ (((True → p2) ∨ True) ∨ (False ∧ ((p1 → False) → p3)))) ∧ p5) ∨ p1)))) ∨ (p1 → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223383027040283073107685532421 : ((True ∨ (p3 ∨ p3)) ∧ ((p5 ∨ (p4 ∧ p5)) ∨ (((True ∧ (True ∨ (p2 → False))) → (((p2 ∨ p3) → p2) ∧ p2)) → (p1 ∨ (p2 ∨ p2))))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∧ (True ∨ (p2 → False))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



