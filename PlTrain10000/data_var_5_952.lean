variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40569643705055577474277055055 : ((((p5 → (((p1 ∧ p5) ∨ ((p2 ∧ ((p5 ∧ p4) ∧ (p5 ∨ p5))) ∨ ((False → ((p5 ∧ p2) ∨ False)) → p2))) ∨ p5)) ∨ p4) ∨ p1) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774102193205489224073423675312 : (((False ∨ ((p5 ∨ (((p3 ∧ p1) ∧ ((False → ((((True → ((p3 → p4) ∧ p3)) ∧ p2) ∧ p2) ∧ True)) ∨ p4)) ∨ p5)) ∨ (p2 → True))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173907038654388827774126079250 : (((((((False → p4) ∨ p5) → p2) ∨ (((p1 ∧ p2) → p5) ∧ p3)) → p1) → p4) → ((p3 ∧ (p3 ∧ p2)) ∨ (((p3 ∧ p3) ∧ False) → p2))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_237932157468282777831707806444 : ((True ∨ False) ∧ (((((p1 → p4) ∧ (p5 ∨ (((True ∨ ((p4 ∧ p3) ∨ p2)) ∧ True) ∨ (True ∧ True)))) → (False ∨ (p4 → p1))) ∧ True) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255256639183006100018480856404 : ((p4 ∧ p5) → ((p2 ∨ ((p1 ∨ (p2 → False)) → ((False ∨ False) ∨ (True ∨ (p3 ∧ ((p2 ∨ p5) ∨ (p2 → p1))))))) ∧ (p2 ∨ (p5 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230457463460726785142068341540 : (((p5 ∨ p1) ∧ p4) → (((True → ((p5 ∨ (p2 ∨ ((p5 → p5) ∧ p3))) ∨ ((p5 ∨ p3) → ((p5 → p4) ∧ p3)))) ∨ p2) ∨ (True ∧ p1))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206976724408806497907665168991 : ((((p3 → (p4 ∧ p3)) → p2) ∧ p1) → ((p5 ∧ (False ∨ (p4 ∧ ((p5 ∨ False) ∧ (((True ∧ True) ∧ p2) → False))))) → (p2 → (True ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h1.left
      let h14 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_239588775602111254790373242546 : ((p3 ∨ True) ∧ ((((p1 → (p5 ∨ p2)) → ((p2 ∨ p5) ∨ ((p2 ∧ p3) ∨ (p2 → (True ∨ p1))))) ∧ (p3 → p4)) ∨ (p4 → (True ∨ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204447559013996936495302903610 : (((((p4 ∨ p4) → p1) ∧ p2) ∨ p4) ∨ (p4 ∨ (((p3 ∨ (p4 → (True ∧ (((False ∨ (True ∧ True)) ∨ p3) ∨ (p2 → p4))))) ∨ p3) ∨ p4))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46529346144095918914775685574 : ((((p3 ∧ p2) ∨ (((p1 ∨ (p5 ∨ (((((((p3 → p2) ∧ p2) ∧ True) → p3) ∧ p4) ∧ True) ∨ p5))) → p1) ∨ p4)) ∧ (p3 → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147827886443446794352559429501 : (((False ∨ (p1 ∨ (((False ∧ (True → p2)) ∨ (p4 ∨ (p5 → ((p4 ∧ True) ∧ p5)))) ∨ (True → False)))) → p1) ∨ (p4 → ((p2 → p4) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351762273738969835978625910084 : (p4 → ((((p4 ∧ (False ∨ p3)) ∨ p3) ∧ ((p3 ∧ ((p4 ∨ p5) → p2)) ∨ p5)) → (p2 → ((p2 → (p1 ∧ (True → (p3 → False)))) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50448723952951144092683851139 : (((p2 ∨ (((p1 → ((p1 ∧ (True ∨ p4)) ∨ (p3 → p2))) → p4) ∧ (p5 → (False → (p2 ∧ p4))))) ∨ (p2 → (p2 ∧ (p4 ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117663360023414937692532420338 : ((p3 ∧ ((p4 → ((True → (True ∨ ((((p5 ∨ p3) → (p1 ∧ True)) ∧ False) → (p4 → False)))) ∨ False)) → (p2 → (p3 → p1)))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67430664245561503539636258730 : ((p1 → ((p5 ∧ ((p2 ∨ ((((False → ((True → p4) ∧ ((False → p2) ∨ p5))) ∨ p3) → (p4 ∨ p2)) → p5)) ∨ False)) → (True → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729662078506682422777979396737 : (((((False → p2) ∨ False) → (((True ∧ p2) ∨ (((True → (False → p4)) → True) → (False ∧ (((p3 → False) → p1) ∨ True)))) ∨ (p5 → p5))) ∨ p3) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45037912020414640505140254082 : ((((p4 ∨ p1) ∨ (False → (p3 ∨ (((p5 → p3) ∧ p1) → (p4 → (False ∧ ((p2 ∧ (p1 ∧ p1)) → ((p1 → False) → p2)))))))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90918956959219389302573124636 : (((True → False) ∧ ((((p4 ∨ p3) → (((True ∨ ((p5 ∧ p3) ∨ False)) ∨ (p3 ∧ p2)) ∨ p1)) ∧ ((p4 → p4) ∨ (p5 ∨ p5))) ∨ p3)) → p5) := by
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
    cases h6
    case inl h7 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h9 := h2 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h12
  case inr h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h14
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41964577565832659227785639078 : ((((p5 ∧ p5) ∧ (((((p1 ∧ p3) → ((p3 ∧ p5) → (p4 → (True ∨ ((True ∨ p3) ∨ (p3 → True)))))) → p1) ∧ p4) ∧ False)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351942848848575972012252533565 : (p4 → (((p4 ∨ p3) ∧ (((False ∨ (p5 → True)) ∧ p1) ∨ p4)) → (((p3 ∨ p4) → (((p5 ∨ False) ∧ True) → (p1 → False))) ∨ (p5 → True)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h18 =>
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136546997597259226627223273644 : ((((p5 ∨ p3) ∧ p2) ∨ (((((p5 ∨ (p4 ∨ p4)) ∧ (True → (False → (p3 ∨ True)))) ∧ p5) ∨ (p5 ∧ p4)) ∧ p5)) ∨ ((p4 → p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_17848452539217661364802966937 : ((((((((True ∧ p2) → ((((p5 ∧ p2) → p1) ∨ p5) ∧ False)) → p1) ∧ p4) ∨ (p2 ∧ p4)) ∨ p5) ∨ ((p5 → True) ∨ (p1 ∧ p3))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56713376476740569418852063095 : ((((p5 ∧ p4) ∨ True) ∧ ((p1 ∨ p1) → (((((((True → p3) → p2) → (False ∨ True)) → False) → p4) ∨ (p3 ∧ (True ∨ True))) ∨ False))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (((True → p3) → p2) → (False ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : (((True → p3) → p2) → (False ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h9
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42666911476989467304528547012 : (((p4 ∨ (((p4 → p4) → p5) ∧ ((((p4 ∧ (((True ∧ (p5 → p1)) → p3) → ((p4 ∧ False) ∧ p3))) ∨ False) → p5) ∨ p1))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174176480417910882063979395387 : (((p4 ∧ ((True ∧ p3) → ((p2 ∨ ((p3 ∧ p2) → True)) ∧ p4))) ∨ (p1 ∨ p2)) → ((((p1 ∨ (p3 ∨ True)) ∧ True) ∧ p3) ∨ (False ∨ True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150180400833626715760043816268 : ((p1 → (p4 ∨ ((p2 → p5) ∨ (((p2 ∨ p1) ∧ ((p2 ∧ ((p3 ∨ (p1 ∧ p1)) ∧ p4)) ∨ p1)) ∧ p5)))) ∨ (((False → p3) ∨ p2) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44150509694195134368930851759 : (((((p4 ∨ (((p2 ∨ (p1 ∧ p4)) ∨ False) ∧ (p5 → (True → ((False → (True → True)) ∨ False))))) ∨ p4) → (p1 ∨ (p5 ∧ False))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41115897713451729280721570906 : ((((False ∨ ((p5 ∨ (((True ∧ p5) → (p5 → True)) ∨ p5)) ∧ ((p1 → (p4 ∨ (p1 ∧ p5))) ∨ p2))) ∧ ((p5 ∧ p1) → p3)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135193549853877867115128004204 : (((((p3 ∨ p5) ∨ ((((False → (((p1 ∧ p3) → True) ∨ p4)) ∧ (p2 ∧ p5)) → p5) → p2)) → p5) → (p3 ∧ p5)) ∨ ((p1 ∧ p4) → p4)) := by
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
theorem thm_5_vars_208249985981973409017593114016 : (((p3 ∧ p2) ∧ ((p1 ∨ False) ∧ p4)) → (((p2 ∧ False) ∨ ((((p4 → (((p3 → False) ∧ p1) ∨ p2)) ∨ (p3 ∧ p5)) ∧ p2) → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156612792698268470758657947050 : ((((p1 ∨ (True → ((p4 ∧ ((p5 ∧ p5) ∨ (p1 → True))) ∧ ((p5 ∨ p3) → p3)))) ∧ p5) ∧ p2) ∨ (((p5 → p2) → p3) → (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213612888629019415245114832686 : ((((False ∧ p1) ∨ p5) ∨ p2) ∨ ((((p2 ∨ (p1 ∧ (True ∧ (p3 ∧ ((True → True) ∧ (p4 ∧ p5)))))) → ((p3 → True) → False)) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250100584827400647982699292028 : ((True → p4) ∨ (((((p5 → True) ∨ (True ∧ (p1 ∨ p2))) → (False ∨ p2)) ∨ (p5 ∨ True)) ∨ (((p1 ∧ (p5 ∨ (p2 → p5))) ∨ True) ∨ p2))) := by
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
theorem thm_5_vars_305414635567764925253195331238 : (p1 ∨ (((p5 → True) → (((p5 ∧ (((p4 ∧ False) ∨ p2) ∨ (True ∧ p2))) ∨ p2) ∨ False)) ∨ ((p2 ∧ p2) ∨ (p3 → (p4 → (p1 → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117451437026414479128831398596 : ((p1 ∧ ((p2 → (False ∧ p2)) ∧ (((p1 ∧ True) ∧ (((p1 ∨ p2) → p2) ∨ (p3 ∨ ((True ∧ (False ∧ p1)) ∨ p1)))) ∨ True))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638206653670525544208621772510 : ((((((p4 ∧ False) ∨ (((True ∨ p1) → p1) ∨ p5)) → (((False → (False → p4)) ∨ ((p2 ∨ True) ∧ True)) ∨ ((p2 → p5) ∨ p4))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39272462250691373332634804638 : (((False ∧ (p3 → ((((True ∧ p2) ∨ (True ∨ ((p5 ∨ p4) ∨ p1))) → (p5 → p1)) ∧ (False ∧ (((p3 ∧ p5) → p2) ∨ p4))))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25044736509583790760396804749 : (((p1 ∨ (False ∧ p5)) ∨ ((p2 ∧ p2) ∨ (((False → p4) ∨ (p1 → (p4 ∨ ((p4 ∧ p2) ∧ (False ∨ ((p1 ∧ True) → p5)))))) ∨ p1))) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755098924049834194277776356944 : (((False ∧ (p1 → (((((p3 ∨ (p4 ∧ True)) ∨ False) ∨ p3) ∨ p2) → (((p3 ∧ False) ∧ p3) ∨ (((p5 → False) ∧ p2) → (p1 ∧ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171327803740490822918080245615 : (((((p5 → False) → ((p2 ∨ (True → ((p3 ∨ p4) ∧ p1))) → p5)) ∨ p3) ∧ p1) ∨ ((p2 ∨ p1) ∨ (p5 → (((p5 ∧ p1) → True) ∧ p5)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111812892508412965521242707144 : (((((True → p3) → (p5 → (False → ((p2 → (p5 ∧ p3)) ∨ (p1 ∨ (True ∨ (p3 ∨ (p2 ∧ False)))))))) → (True ∧ False)) ∨ p5) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205138680918453437399599780240 : ((((p3 ∨ p5) → p2) ∧ (p3 ∧ False)) ∨ ((p5 ∧ ((p3 ∨ (p3 ∧ True)) ∨ True)) ∨ (((p3 ∨ p3) → True) ∧ (p5 → ((p2 → p2) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172549969733393558805618594236 : ((((p3 → False) ∨ p1) ∨ (p3 ∨ (((p4 ∨ (p4 ∧ (p4 ∨ False))) ∧ p2) → False))) ∨ (True ∨ (((p2 → p4) ∧ ((p4 ∨ p5) ∨ p3)) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789142106545075235394485425137 : (((p5 ∨ ((False ∧ (p1 ∨ ((p5 ∧ p4) ∧ (((False ∨ ((p2 → ((False → False) ∧ p1)) ∧ False)) ∧ True) ∧ p4)))) ∨ ((p4 ∧ False) ∨ True))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662265295388312343142847963783 : (((((((False ∧ ((p2 ∧ True) → (False ∨ True))) → p5) ∧ p3) → (p1 → (((p2 ∧ (p3 ∧ p1)) ∧ True) ∨ (p3 ∧ p1)))) → (p5 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785140266198356333185092880694 : (((p4 ∨ (((((((True ∨ p4) ∧ p2) → ((((p4 ∧ p1) → False) ∧ p1) → p1)) → (p4 ∨ True)) ∨ p1) → ((p3 ∨ p1) → p3)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232186056682215640047507803335 : (((False → p1) → False) → ((p5 ∧ (p1 → (False ∨ (((p2 → (False ∧ p2)) → (p3 ∨ (False → p5))) ∧ (True → (p2 → (p2 → False))))))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238010243919592868582755127252 : ((True ∨ p1) ∧ ((p5 ∧ (((((True ∨ (((p1 ∧ False) → ((p5 ∨ True) ∨ p1)) ∨ True)) → p2) ∨ True) ∧ p3) ∨ False)) ∨ ((p3 ∧ p2) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50223643358986433675733977929 : ((((p2 ∧ (p2 ∨ (((True ∧ (p1 → (False ∧ p4))) ∧ (p3 ∧ (p4 → p5))) → (p5 → False)))) ∨ False) ∨ (((p3 ∨ False) ∨ True) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322356096697446004694918743886 : (p5 ∨ ((((False ∧ ((((p1 ∨ ((p5 ∨ p4) ∨ (p5 ∧ p4))) ∨ p5) ∧ p5) ∧ True)) ∧ ((p3 ∨ p2) → p3)) ∨ (False ∨ (p1 ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616699498998353020039021758519 : (((((((((p2 → p5) ∧ p5) ∨ p4) → (p1 ∨ p2)) ∨ p5) ∨ ((p4 ∧ (((p5 ∨ p1) ∨ p3) ∨ True)) ∧ (True → (False → False)))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114256657335365863083602631225 : (((p2 → (p1 ∧ (p3 → (((p1 → p3) → (p2 → (p5 → (False ∨ (False ∨ (p5 ∨ p2)))))) ∧ p3)))) → ((p5 → False) ∨ p5)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637410599122538471706234058720 : (((((((True ∨ p1) → (False ∧ (p4 ∧ p3))) ∧ (p3 ∨ p4)) ∧ (False → ((((p5 → (p4 → True)) ∨ True) ∨ (p5 ∨ p1)) ∧ p3))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47124605419298636378226491862 : ((((((((False ∨ p4) ∧ p2) ∧ p5) ∨ (((p2 ∨ (p4 ∧ (p2 ∨ True))) ∧ p2) ∨ False)) → p3) → ((False ∨ p4) ∨ False)) ∨ (p4 ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647641410434924272815517475686 : ((((p5 → (((False ∧ ((p3 ∨ (True ∨ False)) → p5)) ∧ False) ∧ (p3 ∧ (((True → (((p2 → p2) → p1) ∨ p5)) → p2) ∨ True)))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160914010771881019616086713114 : ((((p5 ∧ (False ∨ p4)) ∨ True) → ((p2 ∧ p2) → (p2 ∨ ((p4 ∨ p4) ∧ (p1 ∧ (p3 → False)))))) → (((p3 ∨ p4) → (p3 ∧ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147500316572692296749967492347 : (((False ∨ (True ∧ (p5 ∧ (((p2 ∨ (p5 ∧ (p4 ∨ p5))) ∨ (False → ((p3 ∨ p5) → p4))) ∧ p5)))) ∨ p2) ∨ (((p3 ∧ p5) → p5) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206310903258957894850184246232 : ((p1 ∨ ((p5 ∧ p4) ∨ (p3 ∨ p2))) ∨ (False → ((p3 ∧ (((((True ∨ p5) ∨ (False ∨ (False ∨ p1))) ∧ True) ∨ p1) ∨ False)) ∧ (p3 ∧ p3)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199726580273492808682750335195 : (((True ∨ (p4 → ((p2 ∨ True) → True))) → False) → (False ∨ ((p3 ∨ (p1 ∨ ((p5 ∨ p3) ∨ ((True → True) ∧ (p4 ∨ False))))) ∨ (p2 ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (p4 → ((p2 ∨ True) → True))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50739646076935355126362451151 : (((p1 ∧ ((p4 ∧ (((p2 → (p2 ∧ (True → (True ∨ (p3 ∨ False))))) → p4) ∨ p1)) ∧ (p4 ∨ True))) → (((p4 ∧ p4) ∨ p3) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684359082301842255019384960973 : ((((((((p3 ∨ p1) ∧ (False ∧ p5)) ∧ (p1 ∨ p5)) ∧ p1) ∨ ((True ∨ p2) → (True ∨ p1))) ∨ ((p2 ∨ ((p4 → p2) → p1)) ∧ p4)) ∨ p4) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157022337623318904830726296037 : ((((False → p5) ∧ ((((p5 → ((p2 ∨ p2) → p1)) → ((p1 ∧ p4) ∧ False)) ∨ False) ∧ p5)) ∨ True) ∨ ((p1 ∨ p5) ∨ ((True ∨ True) → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111553570389893238189940531643 : ((((((True ∧ (p2 ∨ p2)) ∧ ((p5 ∨ p2) ∧ (False → (p1 → ((p2 ∨ p3) ∧ p5))))) → ((p4 ∨ p3) → p1)) ∧ True) ∨ p5) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695264758411924191321342296540 : ((((((p3 ∧ ((p2 ∨ (True ∨ p5)) ∧ (p3 → (p1 → p4)))) → p2) → False) → (p4 ∨ ((p5 ∧ (p2 ∨ (p4 → p1))) → (p3 → True)))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673895409003092246991234252773 : (((((p2 ∨ p1) → (True ∨ (p4 ∧ ((p1 ∧ p2) ∨ (p4 ∨ (p1 → (((True → p4) ∧ (p1 ∨ p4)) → p3))))))) → (p1 ∨ (p3 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258047190049022618498487446764 : ((p4 ∨ p2) → (((((p5 ∨ p3) → p5) → False) ∨ ((p4 → (p5 ∨ p2)) ∧ (((p1 ∨ (p5 → (p2 ∨ True))) ∨ False) ∧ False))) ∨ (p4 → p4))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337365235421421986578697527669 : (p1 → ((((False ∧ p2) → ((p5 ∧ (((p5 → False) ∧ (False → False)) ∨ True)) ∨ p4)) → (((p1 ∧ p4) → p1) ∧ p2)) ∨ ((p4 ∨ p1) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167504135731644843548850919744 : ((((p5 ∧ ((p2 ∧ ((p4 → p3) ∨ p3)) ∧ p2)) ∧ ((False ∨ p5) → p2)) ∧ (False → False)) → (((p3 ∧ p5) → False) → ((p5 → p3) ∨ p5))) := by
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
    exact h7
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317035429924513850238997823389 : (p3 ∨ (p4 → ((((((p1 ∨ p1) ∨ p2) ∧ True) ∨ p3) ∨ (((p2 → ((p5 ∨ p4) → (True → p5))) → p1) ∨ ((p2 ∧ p3) → p4))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632451400327266877104043012500 : (((((p2 ∨ (((False ∧ (p1 ∨ (((((p5 → p3) ∨ (False ∨ (False ∧ (p5 ∧ p5)))) ∧ False) ∧ False) ∧ p4))) ∧ p1) ∨ True)) → p4) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43103381903422353351689452441 : ((((((p1 ∧ p1) → (((True ∧ p3) ∨ ((((p5 ∨ (p5 ∨ p2)) ∧ p5) → False) ∧ p3)) ∨ p5)) ∨ (p2 ∧ (False → p3))) ∧ True) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49460938219309803811213309000 : ((((p4 ∨ ((False ∧ ((((False ∨ p1) → p1) → p4) → p2)) → (False → (p5 → ((p2 ∨ p5) → False))))) ∨ p4) → (p5 ∧ (False → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207396512670794091754155965974 : (((p2 ∧ (p3 → (p2 ∧ p2))) ∨ p4) → ((((True ∧ False) ∨ (p2 ∨ p2)) → ((p3 ∧ ((p3 ∨ p5) ∧ p3)) ∧ p2)) ∨ ((True ∧ p5) → p5))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165205952225718289540779226015 : ((((((p5 ∧ True) ∨ False) ∧ ((p2 ∧ (p5 ∨ (p3 ∧ p4))) → p4)) → p3) ∨ (True ∨ p2)) ∨ (((((True ∨ p2) ∨ p2) → p5) ∧ False) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60200576845470726786202303692 : (((p5 ∨ p5) → ((((((False → True) ∨ (p5 → p3)) ∨ True) ∧ (p1 ∧ (((p3 → True) ∨ (p2 → p5)) → p1))) ∨ True) ∨ (False → False))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124604843952115490844235910254 : (((p2 ∧ ((p4 ∨ (p4 ∨ False)) ∨ False)) ∨ ((True ∨ (p1 ∨ ((p1 ∧ ((True → p1) ∧ False)) → (p1 ∧ p4)))) ∨ (p5 → p5))) → (p1 ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- False on the left can always be used.
          apply False.elim h9
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
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
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h15
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
theorem thm_5_vars_778249165761791768120533091257 : (((p1 ∨ ((p4 → p3) → (((p2 ∧ ((p1 → p1) → ((p4 ∧ (p3 → ((False ∧ (p1 → p2)) → (p2 ∨ p5)))) ∨ p3))) → p1) ∨ True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_327429613667242020310592524158 : (True → ((((True → (False ∧ (p5 ∨ p5))) ∧ (((False → (p2 ∨ True)) → p2) ∨ (False → p3))) ∧ ((p3 ∧ ((p2 → False) → p3)) ∨ True)) → p3)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h13 := h5 h12
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h19 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h20 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h21 := h5 h20
      -- We need to get the left conjuct of h21 based on <expert-advice>.
      let h22 := h21.left
      -- False on the left can always be used.
      apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313142031408316202196065278296 : (p3 ∨ ((((p3 → (True → (((p2 ∧ p4) → p5) ∨ (p2 ∨ (p3 → False))))) → (True → p1)) → (p4 ∨ ((p5 ∧ True) ∨ (p2 → True)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719147841832030715331655386357 : ((((p1 ∧ ((p5 → p2) → p3)) ∨ ((False ∨ (((p4 ∧ p2) ∨ True) → p4)) ∧ ((p4 ∨ ((p3 ∧ (p5 ∧ False)) ∨ (p3 → p2))) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190268968744273153340429111862 : (((((False ∧ (True ∨ p5)) ∨ (p1 ∨ False)) ∨ p1) ∨ p4) ∨ ((((p4 → (((p4 → p3) ∧ p4) ∨ p4)) ∧ p1) ∨ ((p1 → p5) → False)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164946818816552768502971039949 : (((((p5 ∨ (((True → (p1 ∨ (p3 ∧ False))) ∨ p4) ∧ p5)) ∧ (p3 ∨ False)) → False) → False) ∨ ((((p3 ∧ False) → True) ∨ (p4 → p1)) ∨ p1)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70571647448592689907123060713 : (((((p5 ∧ (p3 ∧ ((((p4 ∧ (p1 ∨ p3)) → True) ∨ False) → False))) ∨ ((p1 ∧ False) → (True ∨ p3))) → (p4 ∧ (p2 ∧ p1))) ∧ p2) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 ∧ (p3 ∧ ((((p4 ∧ (p1 ∨ p3)) → True) ∨ False) → False))) ∨ ((p1 ∧ False) → (True ∨ p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h4
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209167968392281836176012606333 : ((p3 ∨ (p4 ∨ (p3 ∧ (p2 ∨ p3)))) → (p5 → (p4 → (p2 ∨ ((True ∧ p2) ∨ ((False ∧ (False ∨ p3)) ∨ (p5 ∨ (p4 ∨ (p5 ∧ p3))))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146618070618073724366128315399 : ((True → (p2 → (((True ∧ (((True ∨ p4) → False) → (((p3 ∧ p5) ∨ (p5 ∧ p5)) → p5))) → False) ∨ p2))) ∧ ((p4 ∨ (p2 ∨ True)) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106754763006741550854101776870 : (((p5 ∧ (p3 ∧ (p5 ∨ (True → p5)))) ∨ (p5 → ((((p3 → p4) → (p4 → p4)) ∧ (p3 ∨ (False → (True ∧ p3)))) ∧ True))) ∧ (p3 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60734640779370185014344898932 : ((True ∧ ((p5 ∨ (False ∨ (False → p1))) → ((((True → (p2 ∨ (p1 ∧ (True → (p5 ∨ (p2 ∨ (False ∧ p4))))))) ∨ True) ∨ True) ∨ p2))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199221127821561078075191764713 : (((p3 ∨ (p4 → (True ∨ (p3 ∧ p1)))) ∧ True) → (((True ∧ (p5 ∨ ((False ∧ (p2 → (p1 ∧ p2))) ∨ p1))) ∧ p1) ∨ ((p5 ∧ False) → p3))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156691805892074829027771160757 : (((((True ∧ (p4 ∧ (p5 → p1))) → (p2 ∧ ((p2 ∧ p4) → p2))) ∧ (p4 → (p5 ∨ p4))) ∧ p5) ∨ (True → ((p5 ∨ (p5 → True)) ∨ p1))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300539299429268027232448756711 : (False ∨ (((p1 → (((True → p5) ∨ (((True ∨ (p3 ∧ ((p4 → True) ∨ p3))) → True) → p2)) → False)) ∨ True) ∨ (((p3 → p5) ∨ False) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225386347572835909179044118661 : (((p2 ∨ p2) ∧ p5) ∨ ((p2 ∧ ((p4 ∧ (p5 ∧ ((p3 → True) → p3))) → (p3 ∧ p1))) ∨ (((((p1 ∨ p4) ∧ p3) → p1) ∧ False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_957439404373606971426065677319 : ((((True ∨ (p5 ∧ p5)) → (((((p2 ∨ (p1 ∧ p3)) ∧ p4) ∧ ((False → p4) ∧ ((p4 ∧ (p4 ∧ p5)) ∨ p2))) ∨ p3) ∧ (p3 ∧ p4))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (p5 ∧ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147098999358030640981692905245 : (((((p2 ∨ True) → p1) ∨ (p4 → (((p2 ∧ True) → (p2 ∧ (True ∧ p4))) → (p4 → (p1 → p5))))) ∧ p4) ∨ ((False → (False → p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616585377572513749541828671964 : (((((((p1 → p3) ∨ (p3 → (p4 ∨ p4))) ∨ (p5 → p4)) ∧ (((True ∨ (p3 ∨ p1)) ∧ (True ∨ (p2 ∨ p2))) → (p2 → p2))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116057598277738201706671290885 : ((((False ∧ True) ∧ p1) ∧ ((((p1 ∧ ((p5 → ((p2 → (p2 ∨ p3)) → p1)) ∧ p3)) → ((p1 ∨ p4) → p5)) ∧ p2) ∧ p4)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60534393236772558520909068814 : ((True ∧ ((((((False ∨ p3) ∧ p3) ∨ (False ∨ p2)) → (((p1 ∧ p3) ∧ ((p5 → True) ∨ p1)) → False)) ∨ ((p2 → p5) ∧ p3)) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137686525849402574049869462913 : ((p1 ∨ (((p5 → p3) ∨ ((False → True) → (((True ∧ (p4 → p4)) → (p5 ∧ p3)) ∨ (p3 ∧ (p3 ∨ p5))))) ∨ p5)) ∨ (p3 → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346362257468097470554769085845 : (p3 → (((p2 ∧ True) → (p1 ∨ ((((((p1 ∧ p1) ∧ (False ∨ p1)) → False) → (True → (p2 ∧ p3))) ∧ (p4 → p5)) → False))) ∨ (p4 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41355418642088374748032551125 : (((((((p1 ∨ p3) → ((p2 ∨ (p5 ∨ (False ∧ True))) → p4)) → (p2 ∧ False)) ∧ p1) → ((True ∧ ((p4 ∧ p4) ∨ p4)) → p3)) ∨ p1) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : ((p1 ∨ p3) → ((p2 ∨ (p5 ∨ (False ∧ True))) → p4)) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h14 =>
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h15 =>
          -- One of the premise coincides with the conclusion.
          exact h7
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h18 =>
            -- One of the premise coincides with the conclusion.
            exact h7
          case inr h19 =>
            -- One of the premise coincides with the conclusion.
            exact h7
        case inr h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- False on the left can always be used.
          apply False.elim h21
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h23 := h8 h10
    -- We need to get the right conjuct of h23 based on <expert-advice>.
    let h24 := h23.right
    -- False on the left can always be used.
    apply False.elim h24
  case inr h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h1.left
    let h27 := h1.right
    -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
    have h28 : ((p1 ∨ p3) → ((p2 ∨ (p5 ∨ (False ∧ True))) → p4)) := by
      -- Implications on the right can always be decomposed.
      intro h29
      -- Implications on the right can always be decomposed.
      intro h30
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h32 =>
          -- One of the premise coincides with the conclusion.
          exact h25
        case inr h33 =>
          -- One of the premise coincides with the conclusion.
          exact h25
      case inr h34 =>
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h35 =>
          -- Disjunctions on the left can always be decomposed.
          cases h29
          case inl h36 =>
            -- One of the premise coincides with the conclusion.
            exact h25
          case inr h37 =>
            -- One of the premise coincides with the conclusion.
            exact h25
        case inr h38 =>
          -- Conjunctions on the left can always be decomposed.
          let h39 := h38.left
          let h40 := h38.right
          -- False on the left can always be used.
          apply False.elim h39
    -- We have shown the premise of h26, we can now drive its conclusion.
    let h41 := h26 h28
    -- We need to get the right conjuct of h41 based on <expert-advice>.
    let h42 := h41.right
    -- False on the left can always be used.
    apply False.elim h42



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246192842425295708943686036295 : ((p4 ∧ p3) ∨ (((((p2 ∨ p4) → (True ∧ False)) → (((True ∨ ((False ∨ p5) → ((p4 ∨ p4) → p1))) ∧ p4) ∧ p1)) ∧ (p3 → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



