variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174103646933246315772378731532 : ((((False → p5) ∧ ((False ∧ ((p1 → (p2 ∧ p4)) ∨ False)) → p1)) ∧ (True → True)) → (p4 ∨ (((True ∧ (p3 ∨ p1)) ∨ p2) → (p2 → True)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166952888762675869608830931860 : ((((p4 ∨ False) → (p3 ∧ (((False → p2) ∧ p5) ∨ (p3 ∧ ((True ∧ p2) ∧ True))))) ∧ p3) → (((p5 ∧ p2) → ((p2 ∧ p1) ∨ False)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318996302516885101830446950878 : (p4 ∨ ((((((p1 ∨ False) ∨ p2) ∨ (p4 ∨ ((p4 ∧ False) → p2))) ∨ p4) ∨ ((p2 ∧ (False ∧ p1)) → True)) ∧ ((True ∨ p2) ∨ (p5 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677593376201631464816851962233 : (((((((p4 ∧ (p1 ∧ False)) → (p4 → (p4 ∨ ((True ∧ ((True → p4) ∨ p2)) ∧ p5)))) ∧ p2) → p4) ∨ (p1 → (True → (p4 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133255767912428938851205933769 : ((p2 → (((p3 → p2) ∧ (((((False → p2) ∧ False) ∨ (((p5 ∨ p1) ∧ (p1 → p2)) ∧ p1)) ∨ p4) ∧ p2)) ∨ p2)) ∧ (p1 → (False ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308735976089567917202998284020 : (p2 ∨ ((p3 → ((((p1 ∨ (((True → (p4 → p2)) ∧ (p1 ∧ ((p1 ∧ ((p5 → True) ∨ p1)) ∧ True))) ∨ True)) ∧ p2) ∧ True) ∨ p3)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231293090683729329757879916007 : (((p5 ∨ p3) ∨ p1) → (((p4 → True) → ((p1 → p4) ∨ p2)) ∨ ((False → (True → (((p3 ∨ False) ∨ ((p3 ∨ p3) → p2)) ∧ p4))) ∧ True))) := by
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h4
      -- False on the left can always be used.
      apply False.elim h4
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h7
      -- False on the left can always be used.
      apply False.elim h7
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h10
    -- False on the left can always be used.
    apply False.elim h10
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_428756088102496371296299734164 : ((((((p5 ∨ p2) ∨ ((True ∧ (p4 ∧ (p4 → ((p1 ∨ (True → p3)) ∧ (p3 ∨ False))))) ∧ (False → p3))) ∧ (False → True)) ∨ (True ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_149120574468512482241507880736 : (((p1 ∧ True) ∧ (p4 ∨ ((True ∧ p3) ∨ ((p2 ∨ (p4 ∨ ((p1 ∧ p5) ∨ (p5 ∧ (p2 → p1))))) ∨ p1)))) ∨ ((True → (p4 ∨ True)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51168418398761524236906851845 : ((((((p4 → (p4 ∧ ((((p2 ∨ False) → False) ∨ p2) ∨ p5))) ∧ True) ∨ False) ∨ (p2 ∨ True)) ∨ (p3 → (True → (p5 ∧ (False ∧ p4))))) ∨ p5) := by
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
theorem thm_5_vars_87065768823423136838905901307 : ((((((p2 ∧ False) ∨ p3) ∨ True) ∨ (p3 → False)) → (((p5 ∨ False) → (False ∨ (False → True))) → (((p4 → (p1 → p3)) ∧ p5) ∧ p2))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p2 ∧ False) ∨ p3) ∨ True) ∨ (p3 → False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 ∨ False) → (False ∨ (False → True))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h4
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174423013218559124956576772254 : (((p2 ∧ ((p2 ∧ ((True ∧ True) → p4)) → p3)) ∨ ((p2 → (p2 ∧ True)) → p4)) → (((p2 → (True ∨ p1)) → False) ∨ (p1 → (p4 ∨ p2)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : (p2 → (p2 ∧ True)) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h9
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h8
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38528387605305587307743781664 : ((((p2 ∧ ((p4 ∧ (p4 ∨ (p5 ∧ (True ∨ p3)))) → (p1 ∧ p5))) → (((True ∨ (p1 ∧ False)) → ((p2 ∧ p4) ∧ False)) ∨ True)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244454364895194140472355574839 : ((False ∧ p2) ∨ (((True ∧ ((p1 ∨ p4) ∨ (True ∨ ((p2 ∧ False) ∨ p5)))) ∧ p5) → (p1 → (((p5 → p3) ∨ p1) ∧ ((False ∨ p1) ∧ p1))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h17 := h1.left
  let h18 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h19 := h17.left
  let h20 := h17.right
  -- Disjunctions on the left can always be decomposed.
  cases h20
  case inl h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- False on the left can always be used.
        apply False.elim h29
      case inr h30 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
  -- Conjunctions on the left can always be decomposed.
  let h31 := h1.left
  let h32 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h33 := h31.left
  let h34 := h31.right
  -- Disjunctions on the left can always be decomposed.
  cases h34
  case inl h35 =>
    -- Disjunctions on the left can always be decomposed.
    cases h35
    case inl h36 =>
      -- One of the premise coincides with the conclusion.
      exact h36
    case inr h37 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h38 =>
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h39 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h40 =>
      -- Disjunctions on the left can always be decomposed.
      cases h40
      case inl h41 =>
        -- Conjunctions on the left can always be decomposed.
        let h42 := h41.left
        let h43 := h41.right
        -- False on the left can always be used.
        apply False.elim h43
      case inr h44 =>
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687444951513355320537988597722 : (((((((p3 ∧ (p2 ∨ p5)) → (False → p5)) ∧ (p5 ∧ (p2 ∨ (p5 ∧ p1)))) ∨ p3) ∧ (True ∨ (p5 → (((p2 → p4) ∧ p3) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208556195513050460125787454632 : (((p3 ∨ p3) → ((p5 → False) ∧ False)) → (((p4 ∧ (p1 ∨ (p4 ∨ True))) ∧ (p2 ∨ ((p5 → p4) ∨ p4))) → (((False ∨ p2) ∨ True) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h23 := h2.left
  let h24 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h25 := h23.left
  let h26 := h23.right
  -- Disjunctions on the left can always be decomposed.
  cases h26
  case inl h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h28 =>
      -- One of the premise coincides with the conclusion.
      exact h25
    case inr h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- One of the premise coincides with the conclusion.
        exact h25
      case inr h31 =>
        -- One of the premise coincides with the conclusion.
        exact h31
  case inr h32 =>
    -- Disjunctions on the left can always be decomposed.
    cases h32
    case inl h33 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h34 =>
        -- One of the premise coincides with the conclusion.
        exact h33
      case inr h35 =>
        -- Disjunctions on the left can always be decomposed.
        cases h35
        case inl h36 =>
          -- One of the premise coincides with the conclusion.
          exact h33
        case inr h37 =>
          -- One of the premise coincides with the conclusion.
          exact h37
    case inr h38 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h39 =>
        -- One of the premise coincides with the conclusion.
        exact h25
      case inr h40 =>
        -- Disjunctions on the left can always be decomposed.
        cases h40
        case inl h41 =>
          -- One of the premise coincides with the conclusion.
          exact h25
        case inr h42 =>
          -- One of the premise coincides with the conclusion.
          exact h42



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246325945334663956410825621417 : ((p4 ∧ p5) ∨ (((p5 ∨ ((p2 ∧ (p3 ∧ (True → p1))) ∨ (p1 ∨ ((True ∧ p3) → ((p1 ∨ p4) ∧ p3))))) ∧ (p5 → False)) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311788740745165758826688171673 : (p2 ∨ (False ∨ (p3 ∨ (((p1 → (p2 → (p3 → (p4 ∨ (p5 ∨ False))))) ∨ (p5 ∧ False)) ∨ (True ∧ (p5 → (True ∨ (p5 → (True ∨ p3))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40808107057777580621360904244 : ((((p2 ∨ (((p5 ∨ p2) → (((True → ((p4 ∧ p5) → p3)) → (False → (((p5 ∧ p4) ∧ p3) ∧ p2))) ∧ p2)) ∧ p3)) → p1) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652181499306896909083664972692 : ((((p2 ∧ ((((p3 ∧ (p3 ∧ (p5 → (((p4 ∧ True) → True) ∧ (p3 → (p4 ∨ p1)))))) → (True ∧ p4)) ∨ p1) ∨ True)) ∧ (False ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234821089955006003114647453388 : ((p5 → (False ∨ p4)) → (((((p5 ∨ ((p3 ∧ (p3 ∧ False)) ∨ True)) → (p1 ∨ p2)) ∧ p3) ∧ (p3 → True)) ∨ ((p2 → False) ∨ (p5 ∨ True)))) := by
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
theorem thm_5_vars_708370323672458794806607448216 : ((((((p1 → (True → False)) ∨ (p1 → p5)) ∧ p2) → (((((False ∧ p3) ∨ p3) ∨ (p5 ∨ p2)) ∨ (True ∨ ((True ∧ p5) ∨ p3))) ∨ p3)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66020038574803187947844609768 : ((p5 ∨ ((((((False ∨ p1) → p5) → (p5 → True)) ∨ (((p1 → p4) ∨ (p4 ∧ p2)) ∧ (p2 ∨ (p1 ∧ p5)))) → (p2 ∨ p3)) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_868395556101417993967695519765 : (((((p1 → False) → (((((p1 → p1) ∧ (False ∨ (p2 ∨ (p2 ∨ (False ∧ False))))) → p1) → p1) ∨ ((False → (p4 → True)) → True))) → False) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 → False) → (((((p1 → p1) ∧ (False ∨ (p2 ∨ (p2 ∨ (False ∧ False))))) → p1) → p1) ∨ ((False → (p4 → True)) → True))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206911700125708901430696892483 : (((((p5 ∨ p5) → p1) ∨ p5) ∧ p4) → ((((((True ∧ p2) ∨ p4) ∧ p5) → (p4 → p2)) → (p1 ∧ (p3 ∧ (p1 ∧ (p2 → p1))))) ∨ p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354612866458822920692667515856 : (p5 → ((((p1 ∨ ((True ∨ p4) → (p5 ∧ (((p5 → (False → p5)) ∧ ((p4 → p1) ∨ p1)) ∧ p1)))) → (False ∨ (True ∧ p1))) ∨ p3) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (True ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61736784094881143211644377669 : ((p1 ∧ (p2 → ((p1 ∨ True) → ((((p3 ∨ (p3 ∨ False)) ∧ p3) → False) ∧ (((False → p2) ∨ True) ∧ ((False ∨ (p2 ∨ p4)) → True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725027199661271556544672011044 : ((((False → (False ∧ p3)) ∧ ((((((True ∨ p2) ∨ (((p1 → False) → p5) ∨ False)) ∨ True) → (p5 ∨ (True ∧ False))) → (p5 ∧ False)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138265680953446684061852342322 : ((p2 → (True → (False ∨ (((p3 ∨ p3) → ((p4 ∧ p1) ∧ (False ∧ p2))) ∧ (p3 ∧ (p3 ∧ ((p3 ∨ p2) → p2))))))) ∨ ((p1 ∧ p3) → p1)) := by
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
theorem thm_5_vars_319742197585155477418610179768 : (p4 ∨ ((((p5 ∨ p1) ∨ p1) ∧ (True → p4)) ∨ (((p5 ∧ (((p2 → p1) ∨ p2) ∨ ((True ∧ (p4 ∧ False)) ∧ p1))) ∨ True) ∨ (p4 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43141220037469084499969472815 : ((((((((p2 ∧ (p1 ∧ p3)) → True) → True) → p3) ∨ ((False ∨ (p4 ∧ ((True ∨ False) ∧ ((p5 → True) ∨ p5)))) ∧ True)) ∧ p1) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41380086930238689937360465080 : (((((((p5 → p3) ∧ (p2 ∨ (p2 ∧ ((p4 → p5) ∧ p2)))) ∨ True) ∧ p5) ∧ (((p5 → (False ∧ p4)) → p3) ∨ (p2 ∧ p5))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658804664209757796966321851891 : ((((p5 ∨ (p2 → ((p4 ∨ p5) ∨ ((True → ((True ∧ ((False ∧ False) ∧ p3)) ∨ (p5 ∨ ((p3 ∨ p5) ∧ p1)))) → False)))) ∨ (p3 → True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_259756668499463001735235481030 : ((p1 → p2) → ((((((p3 ∧ p1) → p4) ∧ True) ∧ True) → ((p4 ∧ p5) → (False ∨ p1))) ∨ (((((p2 ∨ False) → p2) ∨ p2) → p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208951133606228467087444050357 : ((True ∨ (((p5 → True) → p4) ∨ p3)) → ((((p5 ∧ (p3 → (p1 → False))) → (((p1 ∨ p2) → False) ∨ p5)) ∨ (True ∨ p4)) ∧ (False → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304822943860694086062345426360 : (p1 ∨ (((p1 → ((False → ((False ∨ p4) ∧ ((p5 ∧ False) ∧ False))) ∧ (((p1 → False) → (p4 ∨ False)) ∧ (p4 → True)))) → False) → (p5 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → ((False → ((False ∨ p4) ∧ ((p5 ∧ False) ∧ False))) ∧ (((p1 → False) → (p4 ∨ False)) ∧ (p4 → True)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- False on the left can always be used.
    apply False.elim h4
    -- False on the left can always be used.
    apply False.elim h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- False on the left can always be used.
    apply False.elim h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- False on the left can always be used.
  apply False.elim h9
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : (p1 → ((False → ((False ∨ p4) ∧ ((p5 ∧ False) ∧ False))) ∧ (((p1 → False) → (p4 ∨ False)) ∧ (p4 → True)))) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h12
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h12
    -- False on the left can always be used.
    apply False.elim h12
    -- False on the left can always be used.
    apply False.elim h12
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h13
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h15 := h13 h14
    -- False on the left can always be used.
    apply False.elim h15
    -- Implications on the right can always be decomposed.
    intro h16
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h17 := h1 h10
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324390411830246097070328345001 : (p5 ∨ ((((p1 ∨ (p5 → p4)) → True) ∧ True) → (((((p4 ∧ (p3 → p2)) → p2) ∨ (False ∧ p4)) → (True ∧ (True ∧ (p4 → p4)))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347409784813794911566563246842 : (p3 → (((p2 ∧ (p3 ∨ (p1 ∨ True))) ∨ (p2 ∧ p5)) → ((False ∨ (p5 ∨ ((p2 → True) ∨ p2))) ∨ ((p2 → False) → (p3 ∧ (True ∨ p2)))))) := by
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
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746899090484623443997167160070 : ((((p4 ∨ False) → ((((p5 ∨ p2) ∨ (((p1 ∨ p1) ∧ p2) ∨ p3)) → ((p1 → p3) ∨ (p3 ∧ p1))) ∧ (((p2 ∧ p2) ∨ p4) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112705624100391771921990278385 : (((((False → ((p5 → (p3 → (p1 ∧ p2))) ∨ p3)) → (p3 ∨ (p2 ∧ (p5 → False)))) → (True ∧ (p5 → (True ∨ p1)))) → p3) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596054572091251489673110672641 : (((((((p1 → False) → ((p5 ∧ p4) → False)) → (False ∨ p2)) → ((((True ∧ p1) ∧ p5) → ((True ∧ p1) ∨ False)) → (False ∧ p2))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670436531187496837695222730992 : (((((p5 → (p2 ∧ p4)) → ((p1 ∨ (p1 ∨ ((p4 ∧ p4) ∨ ((p5 → p1) ∧ False)))) ∨ (True ∨ (p4 → True)))) ∨ (p3 ∨ (False ∧ p3))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_139604811457312873313909864723 : ((((p1 ∨ (p3 ∧ ((False ∨ (False → (False → (p2 ∧ p5)))) ∧ p4))) ∧ (((p1 ∨ (p1 ∨ p5)) ∧ p3) ∨ p1)) → p2) → ((p5 ∧ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69347197796236312833973673014 : ((p5 → (p2 ∨ ((((p1 ∨ ((True → p2) ∧ p4)) → False) ∧ (((p5 ∧ (True ∨ ((True ∧ p4) ∨ False))) → p1) ∨ p3)) ∨ (p4 ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336257956105584063574188400559 : (p1 → (((((p5 → p3) → p5) ∧ ((p5 → (False ∨ ((True → (False → True)) ∧ p5))) → p3)) → ((p4 ∧ ((p5 ∧ p5) → p3)) ∨ False)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337361736150630914025396530063 : (p1 → (((((p5 ∨ p3) ∨ True) ∧ (((p5 ∧ False) ∧ p1) ∧ (((p1 → True) → True) ∧ p3))) ∨ ((p2 ∨ False) ∨ False)) ∨ (p1 ∧ (p3 → p3)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622770916940107040011463091311 : ((((p4 ∧ (p1 ∨ ((p4 ∨ p1) ∨ (((((p5 ∧ (True ∧ (p3 ∨ (p2 → (p4 ∧ False))))) → (False → p5)) ∧ p1) ∨ p2) ∧ True)))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_147339114369634081016871298655 : ((((p3 → (p5 ∨ (p4 ∧ ((p5 ∨ ((p4 ∨ (p4 ∨ p2)) → False)) → (p3 → True))))) ∨ (p2 ∨ p1)) ∨ p4) ∨ ((p3 ∨ True) ∧ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644147004174575466024565723170 : ((((True ∨ (False ∨ (((p1 ∨ (p4 ∧ p2)) → ((p5 ∧ (p1 ∨ ((False ∧ (p1 ∨ (True ∨ p2))) → p2))) ∧ (p5 ∧ p1))) → True))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310157845941758595884683012666 : (p2 ∨ (((p3 ∨ (p3 → p3)) → (((((p3 → p5) → False) ∧ p1) ∧ p1) ∧ False)) → (p3 ∨ (p2 → (((False ∧ True) ∨ p3) ∧ (p5 ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ (p3 → p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112669333181282443555514876996 : ((((p4 ∨ (((((p1 ∧ ((p2 ∧ p1) ∧ (p2 ∧ True))) ∧ p2) → p4) ∧ False) → (False ∧ p5))) ∨ ((True ∧ p4) ∨ p3)) → p3) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164800847716776912893949155195 : (((((False ∨ p2) ∨ p5) ∨ (((p5 ∧ (p5 → p3)) → (True ∨ (p2 ∨ p4))) → False)) ∨ p3) ∨ ((((False ∨ (p2 → p3)) → p4) → True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215246466017293901468522610174 : ((False ∧ ((True → p2) → p4)) ∨ (((p5 ∨ (p5 ∨ (p1 → p2))) ∨ (((p1 ∨ p5) ∨ (p5 ∧ (p2 ∨ (p5 ∧ p5)))) ∨ p1)) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64371556518196962487179142276 : ((p1 ∨ (((p5 → p1) ∧ (p5 → (p3 ∨ (p3 ∨ (((((p4 ∧ p2) → ((p2 ∨ p3) → False)) ∧ (p3 → False)) → False) → p1))))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352783602811853002444029366615 : (p4 → ((True ∨ p5) → (((False ∨ (((p1 → p1) ∨ p4) ∨ (p5 ∨ True))) ∧ ((p5 ∨ (p5 ∧ p4)) ∨ ((p1 ∨ p5) ∨ p4))) ∨ (False ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1757453967366529779877889078 : (((((False ∨ ((True → (False ∧ ((p2 → p2) ∧ (False ∧ False)))) ∨ (p4 ∧ p5))) ∨ (True → p5)) ∧ p3) ∧ p5) ∨ ((False → p3) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125592370759719676980373128995 : (((p4 → p3) ∧ ((True → ((p2 ∨ True) ∧ (((((p3 → False) → p4) ∧ ((False ∧ p4) ∧ False)) ∧ p2) ∨ (False → p3)))) → False)) → (p2 → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (True → ((p2 ∨ True) ∧ (((((p3 → False) → p4) ∧ ((False ∧ p4) ∧ False)) ∧ p2) ∨ (False → p3)))) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h5
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669290559526834898308888115366 : (((((((((p2 ∧ True) ∨ (p3 ∧ ((p4 ∧ p3) ∧ ((p4 ∧ True) → p4)))) → False) ∧ p3) ∧ p4) ∧ (p4 ∧ p4)) ∨ (p4 ∨ (False → p2))) ∨ False) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223901022581719211883852886263 : ((p3 ∨ (p4 → p4)) ∧ ((((False → ((p1 ∧ (False ∨ p1)) ∧ (p2 ∧ True))) ∧ (p2 → False)) ∧ p2) → ((p4 ∧ p4) ∨ (p5 ∧ (True ∧ p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160158103160246274706341475016 : ((((((p1 ∧ p5) ∧ (p1 ∨ p1)) ∧ (p5 → False)) ∨ (((True ∨ p2) → p2) ∧ p5)) ∧ (True ∨ p3)) → ((p4 ∧ (p4 ∨ False)) ∨ (False → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
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
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h12 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h13 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h14 := h6 h13
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h16 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h17 := h6 h16
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h19 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h20 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h21 := h6 h20
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h23 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h24 := h6 h23
        -- False on the left can always be used.
        apply False.elim h24
  case inr h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h28 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h29
      -- False on the left can always be used.
      apply False.elim h29
    case inr h30 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h31
      -- False on the left can always be used.
      apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62883976143832258772572561353 : ((p4 ∧ ((False ∨ p2) ∧ (p4 ∨ ((p3 ∨ (p2 → p1)) → (p1 ∧ ((p5 ∧ ((False → True) → p1)) → (p1 → ((p1 → False) ∨ p5)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_5806551205124980256885348025 : (((((((p2 ∨ (p3 ∨ p3)) ∨ (True → (True → p1))) ∨ p5) ∨ ((p2 ∧ p5) ∨ ((True → p2) → True))) ∨ (p4 ∨ (p4 → p3))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739083016549437581912329288584 : ((((p3 ∧ p4) ∨ (False ∨ (p4 → (((True → p3) ∧ (((False ∨ p5) ∧ (False ∧ (((p2 ∨ p3) → p3) ∨ (p1 ∨ p3)))) ∨ p3)) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113626229030691045771411181509 : (((p2 → (((True ∧ (p1 ∨ (p2 → (p4 ∨ p4)))) ∧ (p4 ∨ ((True ∨ p4) ∧ ((p4 ∨ p1) → False)))) ∧ p1)) ∨ (False ∧ p3)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171782423944667917340412372327 : (((((True → (((p4 → p1) ∧ False) ∧ (p1 ∧ p1))) ∧ p1) ∨ (p4 ∨ p3)) → p5) ∨ ((p2 → (True ∨ p2)) → (p1 → (False ∨ (p1 ∨ p1))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192321674852549145113581652213 : (((p5 ∧ (((p4 ∧ p4) ∨ (p4 ∧ p4)) ∨ True)) ∧ p4) → ((((p2 ∨ (p1 ∨ p2)) → p5) ∧ (p3 ∧ p2)) ∨ ((False ∨ p1) → (False ∨ p1)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h20
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178269443499481245412605224664 : (((((p1 → (False → p2)) → p4) → ((p4 ∧ p2) → False)) ∧ (False → p4)) ∨ ((p3 ∨ ((p1 ∧ p2) → (p2 ∨ p4))) ∨ ((p3 → p5) ∨ p4))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229050741683186723887973954948 : ((p5 ∨ (p3 ∨ p3)) ∨ (((((p4 ∧ ((p3 → False) ∧ p1)) ∨ (False → False)) ∨ p5) ∨ ((True ∧ p5) ∧ ((p4 ∧ (p1 → p2)) ∨ p3))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111694088097524311963220944346 : (((((((((p1 ∧ p3) ∨ (((p4 ∨ (p5 ∧ p2)) ∨ p2) ∨ True)) ∨ p4) ∨ True) ∨ (p5 ∧ (p4 → False))) → False) → p2) ∨ p5) ∨ (p1 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p1 ∧ p3) ∨ (((p4 ∨ (p5 ∧ p2)) ∨ p2) ∨ True)) ∨ p4) ∨ True) ∨ (p5 ∧ (p4 → False))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346920377551482703969869144938 : (p3 → ((p2 ∧ (((p5 → p4) ∨ p2) ∧ ((((p2 → (p5 ∨ (False → p2))) ∧ True) ∨ False) ∧ True))) ∨ (p4 ∨ ((p2 ∨ (p1 ∧ p3)) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810445503444900772205435856996 : (((p5 → ((((True → p1) ∧ True) → (p1 → (p1 ∧ p5))) → ((False ∨ (((p2 ∨ p2) → False) ∨ ((p3 ∨ True) → (False ∨ True)))) ∨ False))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h3
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260798846955414557415470079794 : ((p3 → p5) → ((p2 → (False ∧ False)) ∨ (True ∨ (((p4 → p5) → True) ∧ ((((p3 → (p5 ∧ ((p4 → False) → p5))) ∧ False) → p3) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45030555400099935138103682828 : ((((p2 ∨ p1) ∨ (True → (((p1 ∨ p5) ∨ p3) ∧ (p1 ∧ (((((((p4 ∨ p3) ∨ p1) → p4) ∧ True) ∧ p3) ∧ p2) ∧ p5))))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134459398198893217045030205050 : ((((((p5 → p5) ∨ ((p4 ∧ p5) ∨ p1)) → (p2 ∨ ((p1 → (p5 ∨ (p5 → (True ∨ p2)))) ∧ p2))) ∧ True) → False) ∨ ((p3 ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789650702309329020761529457620 : (((p5 ∨ ((p4 → (p1 → ((True ∧ False) ∨ p4))) ∧ ((p3 ∧ ((((p4 → False) ∨ ((p2 ∧ p3) ∨ p1)) ∧ True) ∨ (True → p2))) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45711929986011022083498373537 : (((True → (((((True → (p5 ∨ ((True ∧ False) ∨ True))) → p2) → ((p3 ∨ p3) ∨ (p2 ∧ p4))) → p2) ∧ ((p3 ∧ p4) ∨ False))) → p3) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670957925348582314646484550969 : ((((p4 ∧ (p1 → ((p3 ∧ (p3 → (((p2 ∨ ((p2 ∧ p4) ∨ p4)) ∧ p2) → (p5 ∨ (p1 ∧ p2))))) ∨ p4))) ∨ ((False → True) ∨ False)) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739326036422405803607738929147 : ((((p4 ∧ p4) ∨ (((((p2 ∨ False) ∨ (p2 ∨ True)) ∧ ((((True ∧ (p4 ∧ p3)) → p2) → p4) → ((p2 → False) ∧ p3))) ∨ p3) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746338222030389097637968023423 : ((((p2 ∨ False) → ((True ∧ (((True ∨ ((False → p5) ∨ p1)) → (((p4 ∧ (p4 ∧ p2)) ∨ (p4 → p2)) ∧ (p2 ∨ p5))) ∨ False)) ∨ p2)) ∨ p2) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68630892857409309287288797269 : ((p4 → ((p3 ∨ (True ∧ ((p4 ∨ ((p5 → False) → p5)) → (((p3 ∨ (False → False)) ∧ (((p3 ∧ p2) → p2) ∨ p1)) ∧ False)))) ∨ p4)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695628108997022876180579250310 : ((((((p3 ∨ (p1 ∨ True)) → (p2 ∧ p5)) ∨ ((True → (p2 → False)) ∨ p1)) → ((False → (((p1 → p5) ∧ (False → p3)) ∨ True)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655347120910463577094468118695 : ((((((p2 ∨ ((((p2 → (p5 → (p5 ∧ p3))) ∧ (False ∨ (p1 ∧ p2))) ∧ p1) ∨ (p4 ∧ True))) ∧ True) ∨ (p2 ∨ p4)) ∨ (False → True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_626288922873333769196498235115 : ((((p3 → (((p3 ∨ True) → False) ∨ ((((((p1 ∨ (p5 → True)) ∧ (((p2 ∨ False) ∧ p4) → p4)) ∨ True) ∨ True) ∧ p5) → p1))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50617419243582094238948860842 : (((((((((False ∨ (False → p1)) → p5) ∧ (p4 ∧ True)) ∧ p1) → p2) → False) ∧ ((p4 ∨ p5) ∨ p3)) → ((p5 ∧ (p3 ∨ p4)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115155153924583807104409812081 : (((p1 → ((p4 → (((p5 ∧ p5) → p2) → (p1 ∧ p2))) → False)) → ((p2 ∨ ((False ∨ p4) ∨ (p2 → p5))) ∧ (p3 → True))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686188727024518439209491695524 : (((((p3 → ((False ∨ (False ∨ p4)) ∧ (p1 ∨ (p2 ∨ False)))) ∧ ((p4 ∨ p5) ∨ (False ∧ True))) → ((p4 → ((False → p5) → p5)) → p5)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h7 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h8 := h2 h7
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : (False → p5) := by
        -- Implications on the right can always be decomposed.
        intro h10
        -- False on the left can always be used.
        apply False.elim h10
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h11 := h8 h9
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- False on the left can always be used.
    apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119387775861998448068751071228 : ((p4 → (((p5 ∧ (True ∧ ((p2 → True) ∧ ((((True → p1) → (p4 ∧ (p4 → p5))) → p1) → (p5 ∨ p3))))) ∧ p2) ∧ p2)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731670129892724726175937092159 : ((((p2 → (p2 ∧ p4)) → (((p2 ∧ ((p3 ∧ ((p2 ∧ p4) → p2)) → (p4 ∧ p5))) → p1) → ((p4 ∧ (p4 ∨ p3)) ∨ (p5 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41342670992282054475248846443 : (((((p5 ∨ (True ∧ (p5 ∧ False))) ∧ (((p2 ∨ (p4 → p1)) ∧ p1) ∧ (p4 → p4))) ∨ ((p2 ∨ p3) ∨ (p5 → (p3 ∨ True)))) ∨ False) ∨ p2) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317035097240103083107173324226 : (p3 ∨ (p4 → (((p1 ∨ (((p2 ∨ p3) → (p5 ∧ p5)) ∧ (True → (p1 ∨ p2)))) → (((False ∧ (p5 ∧ p4)) ∧ p4) ∨ (p2 ∨ True))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689660034916633754611358357350 : ((((((p4 ∧ (p2 ∧ True)) ∧ p5) ∨ ((((p1 ∧ p2) ∨ p4) ∧ (False → p1)) ∧ p2)) ∨ ((((p4 ∧ True) ∧ p1) ∧ True) ∨ (p3 → p3))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_260059080137928215737018907940 : ((p2 → False) → ((True → ((p4 ∨ (False ∨ ((False ∧ p1) ∨ p2))) ∨ ((p3 ∧ p2) ∨ (p4 → True)))) ∨ (((p4 ∧ (p5 ∧ False)) ∧ p2) → p3))) := by
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
  let h7 := h6.left
  let h8 := h6.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351637488399873243434514213643 : (p4 → ((((p2 ∧ (((p3 → p1) ∧ p2) ∨ p5)) → p4) → ((p4 → (p2 → p2)) ∧ False)) ∨ ((True → (True ∨ ((p1 → p3) ∨ False))) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80678403375171817862454459339 : (((False ∨ ((p2 ∧ p5) ∨ ((True ∧ ((True ∨ False) → False)) → (((p5 ∨ (p5 → (p2 → (p4 ∧ True)))) ∨ False) ∧ p4)))) → (p3 ∧ p1)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ ((p2 ∧ p5) ∨ ((True ∧ ((True ∨ False) → False)) → (((p5 ∨ (p5 → (p2 → (p4 ∧ True)))) ∨ False) ∧ p4)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (True ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- False on the left can always be used.
    apply False.elim h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : (True ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- False on the left can always be used.
    apply False.elim h11
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h2
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184567613295852769946499882105 : ((((p1 ∨ (p2 ∨ p5)) → ((False ∧ p3) ∧ p5)) → (True → p2)) ∨ (True ∨ ((True ∧ (p3 ∨ p3)) ∨ (((p3 ∧ (p5 ∨ p4)) → p3) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248681717661724763204794289898 : ((p3 ∨ p2) ∨ ((((p4 ∨ (p5 → (p1 ∨ ((p4 ∧ (True ∧ p1)) ∨ (p1 → ((True → ((p4 ∧ p5) → p1)) ∨ p5)))))) ∨ p5) ∨ p4) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173914347473279343014835028678 : ((((p2 ∨ ((((p4 ∨ True) ∧ True) ∨ (p2 → p3)) ∨ (p4 ∧ p2))) → True) → p2) → (p5 ∨ ((False ∨ p4) → (p2 ∨ ((p3 → p1) ∧ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : ((p2 ∨ ((((p4 ∨ True) ∧ True) ∨ (p2 → p3)) ∨ (p4 ∧ p2))) → True) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173401393695908900988955718726 : ((p4 → (p5 ∨ ((p5 → p1) ∧ ((False ∨ (p4 ∧ ((p3 ∨ True) ∧ p5))) ∨ p5)))) ∨ ((p2 ∧ ((((p4 ∧ p5) ∧ False) ∧ p5) ∧ p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675261888076021649706240624883 : (((((p3 ∨ ((((p4 ∨ p1) ∨ (p5 → (p1 ∧ p3))) → (((p1 ∨ p2) → p4) ∧ p3)) → p4)) ∨ True) ∧ ((p2 ∧ (p2 ∧ p4)) ∨ True)) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19540052468007058554892183278 : ((((p4 → (p2 ∨ (p4 ∧ (((True ∨ p3) → ((True ∧ p2) → p2)) ∨ p1)))) → p3) ∨ ((True → False) → (False ∨ (False ∨ (p4 ∧ True))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



