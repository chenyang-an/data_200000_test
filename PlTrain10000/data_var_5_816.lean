variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40697362844474784661011328469 : ((((((p2 → True) → (True ∨ ((((p3 → (p5 → p4)) ∧ p3) ∧ p2) ∧ p3))) ∨ ((((p1 ∧ p4) ∨ p3) ∨ p3) ∧ p2)) → p1) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354720410745959941360836687438 : (p5 → (((p2 ∨ ((p2 ∧ p5) ∧ (p4 ∨ (p4 ∨ (((p5 ∨ p1) ∧ (((p3 ∧ True) → True) ∧ p2)) ∨ p1))))) ∨ (False ∧ (False ∧ False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61686295827962513989698933334 : ((p1 ∧ (False ∨ (True ∧ (((((False → (p2 ∨ True)) → (p1 ∧ p5)) ∨ p1) ∨ True) ∧ ((((p3 ∨ False) → p5) → (False ∨ p3)) → True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253856908731896433277195968791 : ((p1 ∧ p3) → ((((p5 → p2) → p4) ∨ ((p4 ∧ True) → (p3 ∧ (((False ∨ ((p2 ∨ (p1 ∨ p1)) → True)) ∧ p2) ∧ p5)))) ∨ (p3 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345369248367176129836362826652 : (p3 → ((((((p1 ∧ ((True → False) ∨ (p2 ∨ (p3 ∧ False)))) ∧ p5) ∨ p4) ∧ (((True → ((False ∧ False) → p5)) ∧ p2) → False)) ∨ True) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186661253944454519416385596456 : ((((p4 ∨ (True ∨ (p3 ∨ p4))) → p2) ∧ ((p1 → p2) ∨ True)) → ((p4 ∧ ((p1 → p5) ∧ p5)) ∨ ((p1 → (False → p4)) → (p3 → p2)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h6
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : (p4 ∨ (True ∨ (p3 ∨ p4))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : (p4 ∨ (True ∨ (p3 ∨ p4))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h12
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152668910961780971805131727130 : (((p4 → p1) ∧ (((((p4 ∨ p3) ∧ (p3 ∨ (p3 ∧ p2))) → p4) ∧ p3) ∧ ((True ∧ True) ∧ (p4 → p4)))) → (p4 ∨ ((p2 → p1) ∧ p4))) := by
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
  let h8 := h5.left
  let h9 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h12 : ((p4 ∨ p3) ∧ (p3 ∨ (p3 ∧ p2))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h13 := h6 h12
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113743195527082753377620305933 : ((((True ∨ (((p1 ∨ p1) ∨ (p3 ∨ p5)) ∨ (p5 → (False ∨ False)))) ∧ ((p2 ∨ (p1 → (True → p1))) ∧ p4)) → (False ∨ p1)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319729066714817008964273012973 : (p4 ∨ (((((p1 ∧ p1) ∨ True) ∨ p5) ∧ p3) ∨ (p2 → (((False ∨ (False ∧ False)) ∨ p2) ∨ (p2 → ((p5 ∧ (p5 ∧ (p2 ∨ True))) → False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158764781480410288413935782602 : ((p4 ∧ ((False → p2) ∧ ((((p5 → (p4 ∧ (p2 ∧ p3))) → (True ∨ (p2 ∧ p5))) ∨ p1) → p5))) ∨ (((False → (True → p2)) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160996323701032051439612636988 : ((((p4 ∨ True) ∨ p5) ∨ ((((False → (p4 ∨ p4)) ∧ ((True ∨ p4) → p5)) → (p3 ∨ p4)) ∧ p1)) → (((p4 ∧ True) ∨ False) ∨ (True ∨ False))) := by
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64818469807108061847856502099 : ((p2 ∨ ((((p3 → (True ∨ ((False → p5) ∨ ((p3 ∧ (p2 ∧ (p1 → p1))) ∨ (p5 → (True → p3)))))) → (True ∧ p5)) → p5) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218211089796077785811292200791 : (((p3 ∧ p3) ∨ (p1 → p1)) → ((((p2 ∨ (((((True → (False ∨ (p3 ∨ p3))) → p1) → (p4 → p3)) → p4) ∨ p5)) → p1) ∨ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219254203063219767376520962238 : ((p1 ∨ (p1 ∧ (p5 ∧ True))) → (True → (((False ∧ (((True → False) ∧ (p3 → p1)) ∧ True)) ∨ False) ∨ (False → (p2 ∨ (p1 ∧ (p1 → p2))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207977715197031599633046563391 : ((((p1 → p1) ∧ p4) ∨ (p2 ∧ p5)) → (p3 ∨ ((((p1 ∨ True) ∨ (True → ((p4 ∨ (((p1 ∨ p1) ∨ True) → False)) ∧ True))) → p2) ∨ p4))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42488555597229736569756536691 : (((False ∨ ((p2 ∧ (True → ((((False ∧ (p1 ∧ ((True ∨ (p1 ∨ p5)) ∧ p5))) → ((False ∨ True) ∨ p1)) ∧ p5) ∧ p5))) ∧ True)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356778425881798151041061054775 : (p5 → ((p5 ∧ (p5 ∧ (p5 → (False ∧ False)))) → (p4 ∨ ((False ∧ (((p4 ∨ (p1 ∧ p2)) → (p4 ∨ p1)) ∨ p1)) ∧ ((p4 → p3) → p5))))) := by
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249484405838209699910327840067 : ((p5 ∨ p1) ∨ (((p1 → (False → p1)) → (((p1 ∧ True) → (((False ∧ True) ∧ (p3 → ((p5 ∨ p4) ∨ False))) ∨ p2)) → p5)) ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597078454329122564095785383574 : (((((True ∧ (p4 ∨ ((p2 ∧ p4) ∧ p4))) → (((p5 ∧ True) ∧ ((p1 → ((p2 ∨ (False → False)) → (p2 → p3))) ∧ p5)) ∨ False)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659654793609003556441636060271 : (((((((False ∧ (p5 ∧ True)) ∧ p5) ∨ (p3 → (p4 → ((p3 ∨ True) ∧ ((True ∧ p5) ∧ ((p1 ∨ False) ∧ p4)))))) ∧ p5) → (p5 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307484760693091907514233488965 : (p1 ∨ (True → ((((True ∧ (p2 ∧ (True ∧ ((p2 ∨ p5) ∧ p1)))) ∧ ((False ∨ False) ∨ (p5 ∧ (p4 ∧ p3)))) ∨ ((p2 ∧ p5) → p5)) ∨ p1))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244270555285889789082010389427 : ((False ∧ True) ∨ (((p3 ∨ ((((p2 ∧ p4) ∨ (p4 ∨ p5)) → p5) → p3)) → (p5 ∧ p4)) ∨ ((((p3 ∧ p3) ∧ p2) ∧ (p1 → p4)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112211358179000211706726744466 : (((False ∨ ((p2 ∨ (((p1 → True) ∨ (p1 → True)) ∧ p5)) ∧ (((p5 ∨ ((p5 → p3) → p1)) → True) ∧ (p5 → p1)))) ∨ p5) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258400563013973791256269258631 : ((p5 ∨ p1) → ((((p5 → (p4 → ((p4 ∨ ((False ∨ p1) → p1)) → p1))) → p5) → (((p4 → p1) ∧ p5) ∨ (p1 → (True ∨ True)))) ∨ p5)) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105460359804939448120871017907 : ((((p3 ∧ (p5 ∨ (p1 ∧ (((p4 ∧ p1) → ((p4 ∧ True) ∧ p4)) ∧ p1)))) ∨ (p3 → p5)) ∨ ((p2 ∧ p4) → (True ∧ p4))) ∧ (False → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117482345146246139443690474077 : ((p1 ∧ (p3 ∨ ((False ∧ (p5 ∧ (((False ∨ False) ∨ p2) ∨ (p4 ∧ (p5 ∧ (p1 → (p1 → (p1 ∨ p5)))))))) ∨ (p5 ∨ p3)))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228424195569644938281142613322 : ((False ∨ (p4 ∧ False)) ∨ ((p4 ∨ (((p3 → ((((p4 → p3) → p2) → True) ∨ False)) → (((p2 ∧ p2) ∨ p5) → p1)) → (p1 → p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777237312870101212781140632794 : (((p1 ∨ (((p1 ∨ True) → ((False ∨ (p4 ∨ p5)) → (p3 → (p5 ∨ ((p2 ∨ (False ∨ (True → p4))) ∧ p3))))) ∨ (p1 ∧ (False ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630079509618970172826267847798 : ((((((p3 → (p3 ∨ True)) ∨ ((False ∧ (((((p4 ∧ p3) ∧ (p3 → (False ∨ p3))) → (p5 ∨ True)) ∧ p3) ∨ True)) → p3)) ∨ p2) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64870458933378575411192417411 : ((p2 ∨ ((p1 → (((p1 ∧ ((p2 → p4) → (((p5 → False) ∨ p1) → (True → p3)))) ∨ (False ∨ (True → p2))) ∧ p1)) ∨ (p1 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140138749940612769004103305163 : (((((((p1 ∨ (p5 ∨ p3)) ∨ p5) → p5) ∨ (p1 → (((True ∧ (True ∨ p1)) ∨ p2) ∧ p5))) ∨ True) → (False ∨ p3)) → ((p3 ∨ p2) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p1 ∨ (p5 ∨ p3)) ∨ p5) → p5) ∨ (p1 → (((True ∧ (True ∨ p1)) ∨ p2) ∧ p5))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186523420739665577373010396922 : ((((((p1 → p5) ∨ p2) → (p5 → p3)) ∨ p2) ∨ (False ∧ p4)) → ((False → p4) → (((p4 ∧ p2) ∨ ((p3 ∨ (False → p4)) ∨ p1)) ∨ p2))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336876717250891187997499449147 : (p1 → ((True → (((p5 ∨ True) → ((p5 → (p4 ∨ True)) ∨ (p2 ∨ ((p5 ∧ False) ∨ ((p4 ∧ (p2 ∨ p3)) ∧ (p5 → p3)))))) ∧ p3)) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52959506113408985491090071424 : ((((True → (p3 → (((p1 ∧ True) ∧ p3) ∨ (True ∧ p3)))) ∨ p5) ∧ ((p3 ∨ (p3 ∧ p5)) → ((p1 → (False → (True ∨ p4))) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44851052755041044362065845707 : ((((False ∧ (p4 ∧ p4)) ∨ (((True → p4) ∧ (True → ((((p1 ∨ False) → p1) ∧ ((True ∨ (p4 ∨ p2)) ∨ p4)) ∨ p1))) → p2)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737437208730026584148785030132 : ((((p4 → p5) ∧ ((((((False → (False ∨ p2)) ∧ (p4 ∨ (p1 → p4))) ∨ (False ∨ False)) ∨ ((p3 ∨ p2) → True)) ∧ (True ∧ True)) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780303926022025169922699608108 : (((p2 ∨ (((p5 → (((p4 ∧ ((((p3 → p1) → p2) → (p1 → p3)) → False)) → False) ∧ p5)) ∧ p4) ∨ (True → ((True → True) ∧ True)))) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692486401761668270730776174841 : (((((((((p4 ∧ p3) ∧ False) ∨ p3) ∧ (p2 ∧ p4)) → True) ∨ (True → p2)) ∧ (((p1 ∨ (p1 ∧ p1)) ∧ (p1 ∨ True)) ∧ (True ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167510392490557724775338750395 : ((((((False ∨ p4) → p3) ∧ p4) ∧ (p3 → (p1 ∧ ((True ∨ p2) → True)))) ∧ (p3 ∨ p4)) → ((p3 ∨ (p2 → ((p5 ∧ p5) → False))) ∧ p4)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h10 : (False ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h11 := h6 h10
    -- One of the premise coincides with the conclusion.
    exact h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h18 =>
    -- One of the premise coincides with the conclusion.
    exact h17
  case inr h19 =>
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_380246883529958026729275273152 : (((((((((p3 ∨ p4) ∨ (False → p1)) → (((p2 → p5) → False) ∧ (False ∧ True))) ∧ ((True ∧ p1) → True)) → (p2 → p1)) ∧ p5) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_40252074881143651568334477679 : ((((False ∨ ((p3 → p4) → ((((True → ((True ∨ p1) → p3)) → (((False ∧ True) → (p4 ∧ p1)) → p3)) → p1) ∧ p1))) ∧ p1) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56780793968492566879939016236 : ((((p3 ∧ True) → p2) ∧ (p5 ∨ (p4 ∧ ((True ∨ p1) → ((((True → p2) → (p5 ∧ p5)) → (((p1 → p2) ∧ p2) ∧ False)) → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65631605102316213612390741221 : ((p4 ∨ (((p4 → (p3 ∧ (True ∨ (((p1 → (((p5 ∧ p5) → (True ∧ p4)) ∧ False)) ∨ True) → ((p4 → p5) ∧ False))))) → p2) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702825598766013472979136368657 : (((((p5 ∨ (False ∨ (False ∧ p1))) ∧ (p2 → (p2 ∧ p3))) ∨ (p1 ∨ ((p4 ∧ (((p3 ∨ ((p4 ∨ False) ∨ p5)) ∨ False) ∨ p5)) → p4))) ∨ p5) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h9 =>
            -- One of the premise coincides with the conclusion.
            exact h9
          case inr h10 =>
            -- False on the left can always be used.
            apply False.elim h10
        case inr h11 =>
          -- One of the premise coincides with the conclusion.
          exact h2
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1787572418465403348403999554 : ((((((p4 ∧ p5) ∨ False) → (p1 → p1)) → (p1 ∨ (p3 ∧ p5))) ∨ ((True → ((False → True) ∧ False)) → p4)) ∨ ((False → p5) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598929300656906202905480877899 : (((((False ∨ p2) ∧ (p5 → (((p3 → p5) ∨ p2) ∧ ((((False ∧ (((p2 ∧ p4) ∨ (False → p3)) ∨ p4)) ∧ p3) ∧ p4) ∧ p5)))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115617552352661743791255729283 : (((False → ((p3 ∨ p1) ∧ (p1 ∧ p1))) ∧ ((False ∨ (p1 → (((p1 ∧ (False ∧ False)) ∧ (p2 ∧ (True ∧ p1))) ∨ p5))) ∨ True)) ∨ (False ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712105790795880924509285030 : ((((((p1 ∨ (p3 → p3)) ∨ p2) ∧ True) → p1) ∨ (p4 ∧ ((True ∧ (p2 ∨ (False ∨ (p4 ∧ ((p4 → p3) ∨ p2))))) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114201314402966448464320926962 : ((((p1 ∧ (p4 → ((False → True) → p4))) ∨ ((p2 → (((True ∨ p1) ∧ p3) ∧ p2)) ∧ (True → p1))) → (p1 → (False ∧ p1))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112081047096042744699427542398 : ((((p5 ∧ p4) ∨ ((False ∨ ((p3 ∧ p2) ∨ p3)) → (((p2 ∨ (p2 ∧ (((p3 ∨ p2) → False) → p5))) ∨ p5) → p4))) ∨ p1) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48034160804800668673110676279 : (((((p5 → p2) ∨ (p2 ∨ (False ∧ (True → (p4 → False))))) ∧ (True ∨ (p3 ∨ ((p1 ∨ (p1 → p3)) → (p1 ∨ p5))))) → (True ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679988756309727985921367137305 : ((((((p2 ∨ ((True → p1) ∧ False)) ∧ (((p3 → ((True ∨ False) → p4)) ∨ (p1 → p1)) ∨ p3)) → p4) → (((p5 ∧ p5) → p5) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112724974876550258863583243630 : ((((p4 → ((p5 → ((p1 ∨ p3) ∧ ((p1 ∧ p3) → (p5 ∨ p1)))) ∧ p3)) ∨ ((p1 → (True ∨ p5)) ∨ (p3 → p4))) → p4) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336330006407991312548277629869 : (p1 → ((((p3 → p5) → p4) ∨ (p4 ∧ (((p4 → ((p2 ∨ p5) → p3)) ∨ (True ∧ ((True ∨ (True ∧ True)) ∧ (p4 → p1)))) ∧ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60750697553584370750981445642 : ((True ∧ (((p3 → False) → p5) → ((p2 ∨ ((True ∧ p1) ∨ (((p1 ∧ p3) → (p5 → (False ∧ (True ∨ True)))) ∨ p2))) ∨ (p3 → p3)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703115829947685468985024100719 : (((((p4 → False) ∨ ((p5 ∨ ((False ∧ p2) ∧ p3)) ∨ p5)) ∨ ((((p4 → (p2 → True)) ∧ p2) ∧ (p5 ∨ ((True ∨ True) ∨ True))) → p2)) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75864362042829866719480561790 : ((((False ∨ (((p4 ∧ p5) ∨ p5) → ((p4 ∧ p3) → (p2 ∨ (((False ∨ (p3 ∧ (p5 → (p3 → True)))) ∨ p5) ∨ p4))))) ∨ False) → False) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∨ (((p4 ∧ p5) ∨ p5) → ((p4 ∧ p3) → (p2 ∨ (((False ∨ (p3 ∧ (p5 → (p3 → True)))) ∨ p5) ∨ p4))))) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h2
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197112073540007279343046276012 : (((False ∨ ((p1 → (p4 → p5)) → p4)) ∨ True) ∨ (False ∨ (p1 ∧ ((p2 → p4) ∨ ((p2 ∨ ((((True → p5) → p5) → p3) ∨ p3)) → p1))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53854173529473323716811814454 : (((((False ∧ p5) ∧ False) ∨ (((True ∧ p4) → False) ∧ p4)) ∨ ((p1 ∧ (((((False ∧ p1) ∧ p3) ∨ p2) ∧ p5) → p4)) → (True ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106560868381174114291216437262 : ((((p1 ∨ ((p3 → p4) ∨ (p3 → p1))) ∧ p4) → ((((False ∧ p4) → (False → p1)) → (((p5 → p1) ∨ p2) → p4)) ∨ False)) ∧ (p4 ∨ True)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h16
      -- Implications on the right can always be decomposed.
      intro h17
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h19 =>
        -- One of the premise coincides with the conclusion.
        exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59491873204471019043497626490 : (((p1 → p5) ∨ ((p3 → (((((p3 ∨ (p4 ∨ (p1 ∨ (p3 ∨ ((p3 ∨ True) ∨ (p5 ∧ True)))))) ∨ p1) ∨ p1) ∨ p2) ∧ p4)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44199603035154787196927118546 : (((((((((p1 ∧ (p1 ∧ True)) ∧ p4) ∨ p3) ∨ p3) ∨ True) ∧ ((p1 ∨ False) → (p2 ∨ p4))) ∧ ((p3 → (p2 ∨ p4)) ∨ True)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720730093043427621567780310811 : (((((False ∧ (True → p2)) → True) → (p1 ∨ (((((((p4 ∨ p1) → True) ∧ p3) ∨ False) ∨ ((True ∨ p4) → False)) ∨ p5) → (p4 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241528741455354833500720322929 : ((False → p3) ∧ (((True ∨ (p4 ∧ (p3 ∧ False))) → ((True ∧ ((p2 ∨ False) → p1)) → ((p1 → (p3 → False)) → (p2 → p5)))) ∨ (True ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253741050393993278151724470623 : ((p1 ∧ p1) → (((False ∨ (p3 ∧ ((p2 → (True → p1)) → ((((p5 → p1) ∨ p4) ∧ True) ∧ p3)))) ∨ p2) ∨ ((p1 ∧ p1) ∧ (True → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185006555006846094740884311507 : (((p5 ∧ p4) ∧ ((((p1 ∨ p4) ∨ True) → (True ∧ p3)) → p5)) ∨ (p3 → (p2 ∨ ((True ∧ (False ∧ (p2 → (False → (False ∧ p5))))) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173181912563154266662586104144 : ((p4 ∨ ((p1 ∧ (p5 ∨ True)) ∨ (((p1 → False) ∧ False) ∧ ((p5 → True) ∨ True)))) ∨ ((p4 → (p2 ∧ p5)) ∨ (p5 → ((p5 → p5) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192375810161695593793246898697 : ((((((True ∨ (False → p5)) ∨ p2) ∧ p2) ∧ p2) ∨ p2) → ((p5 → (((True → (p4 → p2)) ∨ ((p1 ∧ False) ∧ p3)) → (p4 → False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
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
theorem thm_5_vars_184138164103948680747116057928 : (((p4 ∧ ((p2 ∨ ((p1 → p2) → p5)) ∧ (p3 ∧ p4))) ∨ p1) ∨ ((True → ((((((p1 ∧ p4) → p2) ∨ True) ∨ p1) → True) ∨ p5)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60723858176631823092521776090 : ((True ∧ (((p3 ∨ p5) ∧ (False ∨ p2)) ∧ (True ∧ ((True ∨ (p2 ∨ p4)) → (p1 → ((p4 ∧ ((p4 ∧ (False ∨ p5)) ∧ p4)) ∧ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307451504133374280347803687326 : (p1 ∨ (p5 ∨ (((False ∧ (p1 ∧ p5)) ∧ p2) ∨ (((True ∨ False) → p5) → (((p5 → ((p1 → True) ∨ ((False ∧ p2) ∧ p2))) ∨ p4) ∨ p4))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315371176347019642042074241803 : (p3 ∨ ((p3 ∨ (True ∨ p2)) ∧ (((p4 → p4) → ((((False → (p2 ∧ False)) ∨ p4) ∧ ((True ∧ p4) ∧ False)) ∨ p5)) ∨ ((p3 → True) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686214539772490557038789137629 : ((((((((p4 ∨ True) → (p2 ∧ p2)) ∧ (p3 ∨ True)) ∧ p2) → (p2 → (p1 ∧ (p5 → False)))) → (((False → False) ∨ True) → (p1 ∨ True))) ∨ p1) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39093655966817138731914813377 : ((((True → p1) ∨ (p1 ∧ (((False ∧ p3) → ((p5 → p1) ∧ (p4 ∧ p2))) ∧ (False ∨ (((True ∧ p3) ∨ (p2 ∨ p2)) → p5))))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153543134926690751400885076174 : ((True → ((p1 ∧ ((False ∧ p2) ∧ p2)) ∧ (((True ∨ p4) → p3) ∧ (p4 ∧ (p4 → (p2 ∧ (p4 ∧ True))))))) → (((p5 → p4) → p4) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173947971422666463446517669695 : (((((p5 → p4) → (p2 ∨ ((p5 → p2) ∨ p5))) → (True → (False ∨ p5))) → p1) → (((p1 ∧ p4) ∨ (False → p5)) ∧ (p2 → (True ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43853156546772251335313007663 : (((((True → ((False ∨ p3) ∧ ((p5 ∧ ((p2 ∧ False) ∧ (p2 → p4))) ∧ (p4 ∧ False)))) ∧ (p1 ∨ (p3 ∨ p3))) ∧ (True → True)) → p1) ∨ p3) := by
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
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h10 := h4 h9
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h16 := h4 h15
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- We need to get the right conjuct of h17 based on <expert-advice>.
      let h18 := h17.right
      -- We need to get the right conjuct of h18 based on <expert-advice>.
      let h19 := h18.right
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328823055101602103528058423830 : (True → (((p3 ∨ (p3 ∨ (p2 ∧ p5))) ∧ (p1 ∨ (True ∨ False))) → (False ∨ (p3 → ((False ∨ (p3 → (p1 ∨ p3))) → (p4 → (True ∨ True))))))) := by
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
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- Implications on the right can always be decomposed.
        intro h15
        -- Implications on the right can always be decomposed.
        intro h16
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h17 =>
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h19 =>
        -- False on the left can always be used.
        apply False.elim h19
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h23
        -- Implications on the right can always be decomposed.
        intro h24
        -- Implications on the right can always be decomposed.
        intro h25
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h26 =>
          -- False on the left can always be used.
          apply False.elim h26
        case inr h27 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h28 =>
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h29 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h30
          -- Implications on the right can always be decomposed.
          intro h31
          -- Implications on the right can always be decomposed.
          intro h32
          -- Disjunctions on the left can always be decomposed.
          cases h31
          case inl h33 =>
            -- False on the left can always be used.
            apply False.elim h33
          case inr h34 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h35 =>
          -- False on the left can always be used.
          apply False.elim h35
    case inr h36 =>
      -- Conjunctions on the left can always be decomposed.
      let h37 := h36.left
      let h38 := h36.right
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h39 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h40
        -- Implications on the right can always be decomposed.
        intro h41
        -- Implications on the right can always be decomposed.
        intro h42
        -- Disjunctions on the left can always be decomposed.
        cases h41
        case inl h43 =>
          -- False on the left can always be used.
          apply False.elim h43
        case inr h44 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h45 =>
        -- Disjunctions on the left can always be decomposed.
        cases h45
        case inl h46 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h47
          -- Implications on the right can always be decomposed.
          intro h48
          -- Implications on the right can always be decomposed.
          intro h49
          -- Disjunctions on the left can always be decomposed.
          cases h48
          case inl h50 =>
            -- False on the left can always be used.
            apply False.elim h50
          case inr h51 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h52 =>
          -- False on the left can always be used.
          apply False.elim h52



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226291586366409536561878327904 : (((p4 ∨ p2) ∨ p5) ∨ ((((p2 → (True ∧ (p2 ∨ (((True ∨ p3) ∨ ((p1 ∨ p5) → p2)) → False)))) ∧ False) ∧ p3) ∨ (True ∨ (p4 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185293574570520492150576707560 : ((p2 ∧ ((True → p4) ∧ (((p4 ∧ (True → False)) ∧ p3) ∨ True))) ∨ (((True ∧ p4) ∧ p5) → ((p3 ∨ (((p4 ∨ p4) ∨ p5) → p1)) ∨ p4))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198345360888467687468638371292 : ((p2 ∧ ((p1 → (p5 ∧ p3)) → (p4 ∧ p3))) ∨ (((((p1 ∧ (p5 ∧ p5)) ∧ p5) ∧ (((p5 ∧ (p1 → p2)) → p2) → False)) ∨ False) → p5)) := by
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
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134181284230675022788535892937 : (((((p3 ∧ p2) ∧ (((True ∨ (False → p5)) ∧ p1) ∨ (p4 ∨ p3))) ∧ (((p3 → (p4 ∧ p5)) → p3) → p2)) ∨ False) ∨ (True → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325881484343185306941390600397 : (p5 ∨ (p4 ∨ (((p3 → (p5 ∨ p5)) ∨ (p5 ∨ True)) ∨ (((p3 → ((p3 → (p3 ∧ p5)) ∨ p1)) → False) → ((p3 ∧ False) → (p5 ∧ p5)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183134779537507026741395631354 : (((p5 → True) → (((p2 → (p3 ∨ p4)) → p1) ∨ (p1 ∨ True))) ∧ ((p4 → (((p4 ∨ p4) ∧ (False → True)) ∨ p3)) ∨ ((p1 → p1) ∧ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763457806941967693590572762231 : (((p3 ∧ (p1 ∧ ((p2 → (((False ∧ (p3 ∨ p5)) → p3) → (p5 ∧ (p2 ∧ (p3 ∧ (p4 → (((True ∨ False) ∧ True) → p4))))))) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226132355009881215422944024279 : (((False ∨ p2) ∨ p3) ∨ (((p5 ∧ True) ∧ ((p5 → ((((True ∧ p2) ∧ p2) ∧ False) ∧ (p3 → ((p5 ∧ (p1 ∨ False)) ∨ False)))) ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_93844233636996918410302583174 : ((p1 ∧ (((((p5 → p5) ∧ p5) → ((((p1 ∨ (True ∨ p4)) ∧ p2) → (p5 ∨ p3)) ∨ (True → p4))) → p5) ∧ ((False ∧ p5) → p2))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (((p5 → p5) ∧ p5) → ((((p1 ∨ (True ∨ p4)) ∧ p2) → (p5 ∨ p3)) ∨ (True → p4))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h17 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148048399058433533665452285325 : (((p4 ∧ ((((((False ∨ True) → ((p5 ∧ (p2 → p5)) ∨ True)) ∨ p5) ∨ True) ∧ p1) ∨ p1)) ∨ (p5 → True)) ∨ (((p3 → True) → p1) ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37529548457111337884680799502 : ((((p1 ∧ ((p4 ∧ True) ∧ (((((p1 ∧ p3) ∧ p5) ∧ p1) ∧ ((False → False) ∨ (p4 ∨ False))) ∨ ((True ∨ p3) → p4)))) ∨ True) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356897115959481548862450040106 : (p5 → (((p3 ∧ (False ∧ p4)) → p2) → (False ∨ (((p5 → p4) → (((p4 ∧ (((p2 → p4) → p5) ∧ (True → False))) → p5) → False)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65982566907434272635790753006 : ((p4 ∨ (p1 → (p2 ∧ (((True ∨ p5) ∨ (((False → p2) → False) → (p4 ∨ ((p3 → ((p3 → p2) ∨ True)) ∨ (True ∨ p1))))) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142619749952518832028547852004 : ((False ∨ (p2 ∧ ((p1 ∨ (p1 ∧ (p1 ∧ (p4 ∨ (((p3 → p3) ∧ (((p4 ∧ p3) ∨ p3) ∨ p4)) ∨ p5))))) ∨ p3))) → ((p4 → p5) ∨ True)) := by
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
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Conjunctions on the left can always be decomposed.
            let h16 := h15.left
            let h17 := h15.right
            -- Disjunctions on the left can always be decomposed.
            cases h17
            case inl h18 =>
              -- Disjunctions on the left can always be decomposed.
              cases h18
              case inl h19 =>
                -- Conjunctions on the left can always be decomposed.
                let h20 := h19.left
                let h21 := h19.right
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h22 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
            case inr h23 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h24 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40108593883355111840225596467 : ((((((((p4 → (((p4 ∨ p2) ∧ ((p2 ∨ p3) ∧ (True ∨ p5))) ∨ p3)) ∨ p1) ∨ True) → (False ∧ p1)) ∨ (p4 ∨ True)) ∧ p1) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624080512522709002922987394429 : ((((p2 ∨ (((p3 ∨ False) → False) ∧ (p4 → ((((False → (p2 ∨ (p4 ∨ False))) → (False ∧ (False ∨ (p3 → p1)))) ∧ p5) ∨ p5)))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118871684224312340918964333343 : ((True → ((p1 ∨ (False ∧ p4)) → ((((p5 → (False → (p2 ∧ ((False → ((False → p5) → p5)) ∨ True)))) → False) ∨ p1) ∨ p3))) ∨ (p4 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301050393759955949241242392730 : (False ∨ (((p1 ∨ (True ∨ (((False → True) → p3) ∨ False))) → p5) ∨ ((p3 ∧ (p5 ∨ (p3 → p2))) → ((p2 ∧ (p1 ∧ p5)) → (p5 ∨ True))))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336185953563738241726078187277 : (p1 → ((((((p1 → (((p4 → p4) ∨ p1) → (((p1 → False) → False) ∨ (p4 ∨ p2)))) ∧ True) ∧ (False → True)) → p3) ∧ (p3 → p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59525815302320759395959320488 : (((p2 → p4) ∨ (((((False → p3) → (((False ∧ False) → p4) ∨ (p1 → (False ∧ p1)))) ∨ (p2 → (p3 ∨ p3))) → False) ∨ (False → p1))) ∨ p3) := by
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
theorem thm_5_vars_350259101553317398367617593095 : (p4 → ((p2 ∧ (((((False ∨ ((((p2 ∨ p2) ∨ (p4 ∧ False)) → p4) → ((p5 ∧ False) ∨ True))) ∨ (False ∧ p5)) ∧ p3) ∨ p2) ∨ p5)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134234989017333990534773889142 : ((((p2 → (p3 ∨ (p4 → p5))) ∧ ((((p2 → (True → p4)) ∧ (True ∧ False)) ∧ (p3 ∧ True)) ∨ (p5 → False))) ∨ True) ∨ (p2 ∨ (p1 → p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



