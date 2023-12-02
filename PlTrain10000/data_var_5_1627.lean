variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790971496247129073638032254452 : (((p5 ∨ (p5 → ((p4 ∨ p3) ∨ (((p1 → p1) → p4) ∨ (True ∧ (p5 ∨ (p4 → ((((p1 → p2) ∧ p4) → (False ∨ p5)) → p1)))))))) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186926252643759300586068493283 : (((p3 ∧ (p3 ∨ False)) ∧ ((p1 ∧ ((p1 → p2) ∨ p2)) ∨ False)) → (p2 ∧ ((((p5 ∧ p2) ∨ ((p4 ∧ p5) ∨ False)) ∧ p4) ∨ (p2 ∨ True)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h11 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h8
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h12 := h10 h11
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h26 =>
      -- False on the left can always be used.
      apply False.elim h26
  case inr h27 =>
    -- False on the left can always be used.
    apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234682031691362413296255928151 : ((p4 → (p4 ∧ True)) → ((((((p3 ∧ True) → p2) ∨ p5) → ((True ∧ (True ∧ p5)) ∨ (True ∧ ((True → p2) ∨ True)))) ∨ False) ∨ (p3 ∨ p4))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
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
theorem thm_5_vars_117722455081110066466515326237 : ((p3 ∧ (p5 ∨ (False ∨ (((p3 → (((False ∧ p3) ∧ p1) ∧ False)) ∨ (True → (p2 ∨ p2))) → ((p4 → (p5 → p3)) → p2))))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136250224360217836068609300245 : (((p3 ∨ (p1 ∧ ((p2 ∨ True) → p1))) ∨ ((p1 ∧ ((p5 → ((p1 ∧ (False ∨ p2)) ∨ (True ∧ True))) ∨ p5)) ∨ p1)) ∨ (p3 → (True ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679310401366159511448968153742 : ((((p2 → ((((((False ∨ p3) ∧ p4) ∧ (p5 ∧ (p2 ∧ True))) ∧ p2) ∨ ((p4 → False) ∧ p5)) ∧ p3)) ∨ ((p3 ∨ False) ∨ (p5 → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328563886741704149119569266330 : (True → ((p2 ∧ ((p1 ∨ (((p1 ∧ ((False ∨ False) → False)) → p4) ∨ p5)) ∧ (p2 ∨ p1))) → ((p4 → p1) ∨ ((True ∨ (p5 → p4)) → True)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h19 =>
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
theorem thm_5_vars_346583141186328202010736663089 : (p3 → ((((((p1 ∧ p5) ∧ True) → (((p4 ∨ (p4 ∧ p5)) ∧ (p3 ∧ (p1 ∨ p1))) ∨ (True → False))) ∨ p5) ∧ p5) ∨ ((p1 ∧ p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137492891873555117949189770866 : ((p5 ∧ ((((p4 ∧ p5) ∧ (((True ∨ (p3 → p1)) → False) → (p5 → False))) → (p2 ∨ ((p2 ∧ p1) → False))) → p4)) ∨ (True ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166504306924257314279535730089 : ((p4 ∨ (((p2 → (p5 ∨ (p1 → (p5 ∨ ((p2 ∨ p2) ∧ p5))))) ∨ (p1 ∨ p2)) ∧ p2)) ∨ ((((p3 → True) ∨ p2) → False) → (p1 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 → True) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245965642118737466977234049990 : ((p4 ∧ True) ∨ ((((p1 ∧ False) ∧ False) ∧ (((((p4 → p1) ∧ (p1 ∧ True)) ∨ (False → p5)) ∨ (False ∧ p3)) ∧ p5)) ∨ ((p3 ∧ p1) → p3))) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116728996027428462586538376768 : (((p3 ∧ p1) ∨ (p2 ∨ (((p4 ∨ ((False ∨ p1) ∨ (p1 ∧ (((p4 → (p2 → p1)) → p1) ∨ p4)))) ∨ (p2 ∨ p5)) ∧ False))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700051395840089560233126291257 : (((((True → (p2 → p2)) ∧ (((p1 ∨ p3) ∧ (p3 → p4)) ∨ p2)) → (p4 ∨ ((p1 ∨ (p5 ∨ ((p5 ∧ (True ∧ p5)) → True))) ∨ p5))) ∨ p3) ∧ True) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802895609884393098545320197055 : (((p3 → ((((p3 → ((((p2 ∨ ((p2 → ((p2 → True) ∧ (False ∧ False))) → p4)) ∨ p5) ∨ p4) ∧ p3)) ∨ (False → p4)) ∧ True) ∧ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728539883441693722343286073347 : ((((p3 → (p4 ∨ p4)) ∨ ((((p4 ∧ (False → (((p5 → (p3 ∨ (p3 ∨ p5))) ∨ p4) ∨ p5))) ∧ (p3 ∧ (p5 ∧ p4))) ∧ p2) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_207436311386253585280991466738 : (((p2 ∨ ((p4 → p2) ∨ p2)) ∨ p1) → ((((p2 ∧ (p4 ∧ (False ∨ False))) ∨ ((False → p2) ∨ (p1 ∨ (True ∧ p5)))) ∨ (p2 ∧ p2)) ∨ p1)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h6
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h7
        -- One of the premise coincides with the conclusion.
        exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344787677862551886418829409139 : (p2 → (p4 → ((((p1 ∧ (((((False ∧ p5) ∨ ((p4 ∨ True) ∧ p1)) ∧ (p3 ∨ False)) ∧ p1) → p1)) ∧ p2) → p3) ∨ (p4 ∧ (p1 → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71033281963725672414985264396 : (((((False ∨ (p4 ∨ (p1 ∨ p1))) → p4) ∧ (False ∨ ((p1 ∨ p2) → ((True ∧ p1) ∧ (p2 ∧ (p1 → (True → (p2 ∧ False)))))))) ∧ p1) → p5) := by
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
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (p1 ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h15 := h13 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84527277222496579663571933158 : (((((p5 ∨ ((p2 ∨ p3) ∧ p2)) ∨ (p4 ∨ p2)) ∨ (False → (p2 ∨ (p5 → p2)))) → ((p4 → (p2 ∨ p4)) → ((p3 → p1) ∧ False))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∨ ((p2 ∨ p3) ∧ p2)) ∨ (p4 ∨ p2)) ∨ (False → (p2 ∨ (p5 → p2)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p4 → (p2 ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149826639240467249557741791696 : ((p1 ∨ ((((p4 ∧ p5) ∧ (p3 → ((p5 → (((True ∨ True) ∨ p4) → p3)) ∧ p2))) ∧ p5) ∨ (False ∧ p3))) ∨ ((False ∧ (p5 ∨ p1)) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37942524882692305212682231831 : ((((True → (((((p1 ∧ True) → (p5 ∨ True)) ∨ (((p3 ∨ (p4 ∨ p4)) ∧ p5) ∨ (p1 → True))) → p2) ∨ p3)) ∧ (p3 → p4)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611326651625326668821642707589 : ((((((p5 ∧ p3) → ((p4 ∨ p4) → ((p1 ∨ (p4 → ((p3 ∨ p5) ∧ (p5 ∧ True)))) ∧ ((p5 → p4) ∧ (True ∧ p4))))) → p1) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776496330336250110542090355465 : (((p1 ∨ (((((p4 ∨ p4) → (True ∧ (((True ∧ p3) ∨ False) ∧ p5))) ∧ ((False ∧ p5) ∨ False)) ∨ ((True → False) ∧ (p2 → False))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217903309409275695367160777907 : (((p3 → (False → p5)) → False) → (((False ∨ p1) ∧ (p4 → (((p5 ∧ True) ∨ (p3 → ((p2 ∧ p2) → (p1 → True)))) → p1))) ∨ (p4 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → (False → p5)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_222328200297760920185006019578 : (((p1 → p5) → True) ∧ ((p3 ∨ (p3 ∧ (((False ∧ True) ∨ (p4 ∧ p3)) ∨ p4))) → (p3 → ((True → (True ∧ (p1 ∨ False))) → (p1 ∨ False))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- False on the left can always be used.
        apply False.elim h16
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h21 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h22 := h4 h21
        -- We need to get the right conjuct of h22 based on <expert-advice>.
        let h23 := h22.right
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h24
        case inr h25 =>
          -- False on the left can always be used.
          apply False.elim h25
    case inr h26 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h27 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h28 := h4 h27
      -- We need to get the right conjuct of h28 based on <expert-advice>.
      let h29 := h28.right
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h30
      case inr h31 =>
        -- False on the left can always be used.
        apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148545734966832455722764384796 : (((((p5 ∧ (p2 ∧ p1)) ∧ (p5 ∨ (p4 ∧ p3))) ∧ p3) ∧ ((p5 → (((p2 → p3) → p1) ∧ p5)) → p2)) ∨ (((False ∧ True) → p1) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69347427316321547972325091842 : ((p5 → (p2 ∨ ((((p5 → (p2 ∧ (False ∧ ((p5 → (p4 ∨ (p1 → p5))) ∧ (p2 → p5))))) ∨ True) ∨ True) ∧ ((True → p4) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322345034864762453189507772337 : (p5 ∨ (((p3 ∧ (((p1 ∧ p2) → ((((False → p1) → p1) ∨ p4) → ((p3 ∨ p3) ∨ p5))) ∧ (p2 ∧ (p5 ∨ p1)))) → (p4 ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233915739374685629316132334920 : ((p4 ∨ (False → p4)) → (((p1 → (True ∧ False)) ∧ (((p3 ∨ p2) → (False → (True → ((p4 → False) ∨ p5)))) ∨ False)) ∨ ((p4 ∨ True) ∨ p4))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354626784782319488399972678701 : (p5 → (((p1 ∧ ((p3 ∧ p4) ∨ (True → (False ∧ (False ∨ ((p3 ∧ (((p4 → (p1 ∨ p3)) ∧ p3) → (p1 ∨ False))) ∧ False)))))) ∨ p3) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234072974763138047863021432371 : ((True → (False ∧ p4)) → (((p2 → ((((p3 ∧ ((p2 ∨ False) ∧ ((p2 ∧ p5) ∨ p2))) ∧ (True ∧ False)) ∨ (p4 → True)) ∨ p1)) → p2) ∨ p4)) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42330317887412778612600825278 : (((p3 ∧ (((p1 → ((p1 ∨ p2) → (p2 ∧ p5))) → (p5 ∧ (p5 ∧ (((True ∧ (p4 → p1)) → (p5 → True)) ∨ p4)))) ∧ p5)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_72439033361658670131256271298 : ((((((p5 ∨ ((True ∨ (p4 ∨ (((p4 → (p1 ∨ p5)) → p3) ∨ (p4 → (p1 → p1))))) → (p3 ∨ p5))) ∨ p5) → p4) ∧ p3) ∨ False) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : ((p5 ∨ ((True ∨ (p4 ∨ (((p4 → (p1 ∨ p5)) → p3) ∨ (p4 → (p1 → p1))))) → (p3 ∨ p5))) ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h4
          case inr h12 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h4
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h5
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200098206778345518899905893877 : ((((True → False) → False) ∧ ((p5 → p2) ∧ True)) → ((((False ∧ False) ∨ ((p5 → p1) ∧ ((True ∨ False) ∨ p2))) ∨ False) ∨ ((False ∧ p4) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353441900858228578822299820973 : (p4 → (p1 ∨ ((p5 ∨ (p5 ∧ True)) ∨ ((((p1 ∨ (p4 ∧ (((True → False) → p5) ∨ p1))) → p1) ∨ p4) ∨ (((p4 ∨ True) ∨ p1) ∧ p4))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40494082806196169593383720199 : (((((p1 → p3) → (((True ∧ (p4 → p1)) ∧ (((False ∧ p1) → p3) ∧ p2)) ∧ (p3 ∧ ((True ∨ (True ∧ p2)) ∧ False)))) ∨ p1) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40507662189884482207304431785 : ((((p2 ∧ ((((((False ∧ ((False → (p4 → (False ∨ p2))) ∨ p5)) ∧ p4) → (True → p4)) ∧ p2) ∨ p5) ∧ (p4 ∨ p2))) ∨ p3) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184265447168060309579445010450 : (((((p3 ∨ (p5 ∧ p1)) ∨ (p5 → False)) ∨ (p1 ∧ p3)) → p5) ∨ (((False → (p1 ∧ p5)) ∨ p2) → (p4 ∨ (((p4 → p1) → p2) → True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40734831299837922421424091453 : (((((((p3 ∨ p5) → p3) → p5) → (False ∧ ((((p1 ∧ (p2 ∧ ((p2 ∧ p4) ∨ p2))) ∨ True) ∧ (p3 ∨ p5)) ∨ p2))) → p2) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53352280733889222055061498491 : ((((((((p1 ∨ True) → (False → p3)) → p5) ∧ p2) ∨ True) ∨ p4) → ((p4 ∧ (p4 ∧ (p5 ∨ (False ∧ ((p3 ∨ False) ∧ p1))))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654368444721346480931707212038 : ((((((((p1 → (p2 ∧ (p5 ∧ p1))) ∧ (p3 ∨ p5)) → p3) → ((((p3 → p4) ∧ p4) → (p2 ∧ p3)) → p5)) ∨ False) ∨ (False → True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_231203102685417728122969663158 : (((p3 ∨ p1) ∨ p1) → (((((False → False) → (p1 → p5)) → p2) ∧ p5) → ((p2 → (p2 ∧ ((p4 → (p4 → p5)) → p2))) ∧ (True ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Implications on the right can always be decomposed.
  intro h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h2.left
  let h12 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h16 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the left can always be decomposed.
  let h17 := h2.left
  let h18 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h21 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h22 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337102652358236992943673030495 : (p1 → (((p5 ∨ ((p5 ∧ p3) ∨ p4)) ∨ ((((p3 ∨ ((p3 ∧ False) → True)) ∧ p5) → (False ∧ (p5 → False))) → (p5 ∧ p5))) ∨ (p3 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225660606386914763891743740078 : (((p2 → p2) ∧ p3) ∨ (p4 ∨ (True → ((((p5 ∧ True) ∧ (p1 ∨ ((p4 ∨ ((p2 ∧ p1) ∨ p5)) → p2))) → (p3 ∧ False)) ∨ (p2 → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214626790364040327677425286167 : (((False → p2) ∧ (p4 ∧ p3)) ∨ (((p4 ∨ (p3 ∨ p4)) → p3) → (((p1 → (p1 → (p5 ∧ ((p5 → (False ∧ False)) ∧ p3)))) → p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319864663839473409172967991257 : (p4 ∨ ((((p4 ∧ p5) → False) → False) ∨ ((((((p2 ∨ True) ∨ p5) ∨ (p1 → (True ∨ p4))) ∧ (False ∨ ((p2 ∧ p1) ∨ True))) ∨ p3) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305863609391253518937517874350 : (p1 ∨ (((p5 → ((p4 ∨ p2) ∨ p4)) ∧ p1) ∨ (p2 → (p2 ∨ ((True → p5) → (((p3 → (p3 ∧ False)) → (p3 → (p1 ∨ p1))) ∧ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801731141852567410517701970365 : (((p2 → ((p2 ∨ (p1 → p5)) ∧ (((False → (((True ∧ p4) ∨ p5) → ((((p1 → p2) ∧ (True → p5)) → p3) → True))) → p3) ∨ True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206246363817327279150922071788 : ((False ∨ ((p4 ∨ (p5 ∨ p4)) ∧ p2)) ∨ ((p5 ∨ ((True ∧ (p2 ∧ (p5 → ((p5 ∧ False) → p4)))) ∧ ((False ∨ True) → p4))) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689550477241940323289541879730 : ((((((True → ((p4 ∧ (p4 → False)) → p1)) ∧ p1) → (p2 ∧ ((p1 → p3) ∧ p1))) ∨ (((False ∨ (p5 ∧ (p1 ∧ False))) → p2) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252585877423212104802424377699 : ((p5 → p3) ∨ (((((False ∧ p2) ∨ ((p4 → True) → ((False ∧ (p3 ∨ p3)) ∧ p3))) ∧ p3) ∧ (p1 → (p1 ∨ p3))) → ((False → p5) → p1))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h10 =>
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : (p4 → True) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h11
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621470662329630779055379977288 : ((((False ∧ (((p5 ∨ ((p2 → ((False ∧ p5) → (True ∨ p3))) → (False ∨ (p1 ∧ (p2 ∨ p3))))) ∨ (p3 ∧ (p2 ∧ p1))) ∨ p1)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_617281295793097600845403192130 : (((((p5 → ((p3 ∧ (p5 → (False ∧ p5))) ∨ p2)) ∨ (p3 ∨ ((((p2 → p5) ∨ p2) ∧ p1) ∨ (((p3 → p5) ∧ True) ∨ p2)))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138163462934842973054547842911 : ((p1 → (((p5 ∧ ((p2 ∨ p5) ∧ (True ∧ p5))) ∨ ((((p1 → p4) ∨ p2) ∧ p4) ∨ p3)) ∧ (p2 ∧ (True ∧ p3)))) ∨ ((p3 ∨ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698446225322492466037165688916 : (((((((p1 ∧ (False ∨ p1)) ∨ p3) ∧ False) ∨ ((True → p5) → p1)) ∨ (((p1 ∧ (False ∧ (p1 ∨ (p1 ∧ p4)))) ∧ p5) ∨ (False ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178534195216205314082979823278 : ((((p4 ∨ False) → ((p5 ∨ (p2 → p1)) → False)) → ((p2 ∧ p1) ∨ p1)) ∨ ((p2 ∧ p5) ∨ ((p1 ∨ p4) → ((True ∨ p2) ∨ (False → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159235816704700112484554486665 : ((p3 → (((p3 ∨ (p3 ∧ False)) ∧ ((p5 ∨ ((((p1 ∨ p4) → p3) → p4) → True)) ∨ p3)) → p4)) ∨ ((p1 → (False → p5)) → (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692796592735524551884487961146 : ((((((p1 ∧ p4) ∧ p4) ∧ ((((False → (p5 ∧ p5)) ∧ p2) ∨ p1) → True)) ∧ ((True ∧ False) ∧ ((True ∧ (p4 → (p1 → p3))) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117601113893639992314012831130 : ((p2 ∧ (p3 ∨ (p2 ∧ ((((p1 ∨ p4) ∧ (p4 → p1)) ∧ (p5 ∧ (p5 ∧ (True ∨ (True ∧ p5))))) → (True → (p4 → p3)))))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309778899006896440832259073580 : (p2 ∨ ((((p4 ∨ ((True → (False ∨ (False ∨ p3))) ∧ p4)) ∧ (p4 ∨ ((p1 ∨ (False ∨ p4)) ∨ True))) ∧ p1) ∨ (p2 ∨ ((False → False) ∨ p5)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199064237703147839775832363502 : (((((p1 ∧ (p2 ∧ p5)) ∧ p4) → p1) ∧ p1) → ((((p3 ∨ p4) → ((p4 ∧ p5) ∧ p4)) ∨ p4) ∨ ((p5 → (p1 ∨ (p3 ∧ p4))) ∨ False))) := by
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60239891385643125775116519518 : (((True → p5) → ((False ∨ ((False ∨ ((((p5 ∨ (p5 → ((p1 ∨ p4) ∧ True))) ∨ (p1 → p5)) → True) ∧ True)) ∧ False)) ∧ (p3 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116739228667904262150091343878 : (((p4 ∧ p1) ∨ (((p5 ∨ (p3 ∧ (p3 → p1))) ∨ (p2 ∧ ((p4 ∧ True) → (((p4 → True) ∨ p4) ∨ True)))) → (p5 ∧ False))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358118973454041227171227066050 : (p5 → (p2 ∨ (((((p4 → True) ∨ True) ∧ (p2 ∨ p5)) ∨ (p2 ∨ False)) → (p4 → ((p2 ∨ (((True → p5) ∧ p2) ∧ (p1 ∧ True))) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1299784063729496283291628036 : ((True → (((False ∨ (p4 → ((((p2 ∨ True) ∨ (p5 → p2)) → True) ∧ (p2 → True)))) ∧ p5) ∧ (p3 ∧ (p5 ∨ (p1 ∧ p3))))) → p5) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80924009152190877363246974444 : (((((((p1 → p2) ∨ (p4 → p1)) ∧ p3) ∧ ((((p2 → p5) ∨ p4) ∨ (p2 → p2)) ∨ (p2 ∧ p1))) → False) ∧ (p3 ∧ (p1 ∧ p2))) → p4) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : ((((p1 → p2) ∨ (p4 → p1)) ∧ p3) ∧ ((((p2 → p5) ∨ p4) ∨ (p2 → p2)) ∨ (p2 ∧ p1))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h7
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h8
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664102187098508883122110746684 : ((((True ∨ (((False ∧ False) ∧ p5) → (p5 → (p1 ∧ ((((False → False) ∧ ((p2 ∧ p4) ∧ p1)) → False) ∨ (True ∧ p3)))))) → (p1 ∨ True)) ∨ p1) ∧ True) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175110466967017998204697711622 : ((p4 ∧ (((p4 ∨ (True ∧ (False ∧ p4))) → False) ∧ ((True → (p2 ∧ p5)) ∨ p3))) → ((((p2 → False) ∨ (False ∨ p4)) ∧ True) → (p2 ∧ False))) := by
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
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h12 := h10 h11
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h15 : (p4 ∨ (True ∧ (False ∧ p4))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h16 := h8 h15
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h1.left
      let h21 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
        have h25 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h24, we can now drive its conclusion.
        let h26 := h24 h25
        -- We need to get the left conjuct of h26 based on <expert-advice>.
        let h27 := h26.left
        -- One of the premise coincides with the conclusion.
        exact h27
      case inr h28 =>
        -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
        have h29 : (p4 ∨ (True ∧ (False ∧ p4))) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h20
        -- We have shown the premise of h22, we can now drive its conclusion.
        let h30 := h22 h29
        -- False on the left can always be used.
        apply False.elim h30
  -- Conjunctions on the left can always be decomposed.
  let h31 := h2.left
  let h32 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h31
  case inl h33 =>
    -- Conjunctions on the left can always be decomposed.
    let h34 := h1.left
    let h35 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h36 := h35.left
    let h37 := h35.right
    -- Disjunctions on the left can always be decomposed.
    cases h37
    case inl h38 =>
      -- We want to use the implication h36 based on <expert-advice>. So we show its premise.
      have h39 : (p4 ∨ (True ∧ (False ∧ p4))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h34
      -- We have shown the premise of h36, we can now drive its conclusion.
      let h40 := h36 h39
      -- False on the left can always be used.
      apply False.elim h40
    case inr h41 =>
      -- We want to use the implication h36 based on <expert-advice>. So we show its premise.
      have h42 : (p4 ∨ (True ∧ (False ∧ p4))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h34
      -- We have shown the premise of h36, we can now drive its conclusion.
      let h43 := h36 h42
      -- False on the left can always be used.
      apply False.elim h43
  case inr h44 =>
    -- Disjunctions on the left can always be decomposed.
    cases h44
    case inl h45 =>
      -- False on the left can always be used.
      apply False.elim h45
    case inr h46 =>
      -- Conjunctions on the left can always be decomposed.
      let h47 := h1.left
      let h48 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h49 := h48.left
      let h50 := h48.right
      -- Disjunctions on the left can always be decomposed.
      cases h50
      case inl h51 =>
        -- We want to use the implication h49 based on <expert-advice>. So we show its premise.
        have h52 : (p4 ∨ (True ∧ (False ∧ p4))) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h47
        -- We have shown the premise of h49, we can now drive its conclusion.
        let h53 := h49 h52
        -- False on the left can always be used.
        apply False.elim h53
      case inr h54 =>
        -- We want to use the implication h49 based on <expert-advice>. So we show its premise.
        have h55 : (p4 ∨ (True ∧ (False ∧ p4))) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h47
        -- We have shown the premise of h49, we can now drive its conclusion.
        let h56 := h49 h55
        -- False on the left can always be used.
        apply False.elim h56



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159668989735152610739912258554 : ((((False ∧ (((((p3 → (p1 ∧ True)) ∧ ((p2 ∨ p2) ∨ False)) → p5) ∧ p3) ∨ p5)) → p4) ∨ p4) → (p5 ∨ (((p1 → p1) → p5) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h9
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190082885997293518900761127834 : ((((((p1 ∨ p4) ∨ False) ∨ p3) ∧ (p1 ∨ True)) ∧ p1) ∨ (True → ((p5 → ((((p2 → p2) ∧ p2) → p3) ∨ (p1 → p5))) ∨ (False → p5)))) := by
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
theorem thm_5_vars_299350625351329767800894762240 : (False ∨ ((((False → True) ∨ p1) → (((p5 ∧ p5) → ((p2 ∨ ((((False ∧ (p4 ∨ p5)) → (p5 ∨ p1)) → False) ∧ p3)) ∨ True)) ∨ False)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59483899124814817854709204258 : (((p1 → p3) ∨ (p2 ∨ ((p1 → ((False ∧ p1) ∧ (p4 ∧ (True ∨ (((((False ∧ p4) ∨ p1) ∧ False) → p5) ∨ p2))))) → (p5 ∨ True)))) ∨ p1) := by
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
theorem thm_5_vars_60304943444004661111304310261 : (((p1 → p2) → (p3 ∨ ((p5 → ((p1 ∧ (p3 ∧ ((p4 → p1) → ((True → (p2 ∧ True)) ∧ ((p1 ∧ p4) ∨ p2))))) ∧ p3)) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344365064691672898896233044624 : (p2 → (p4 ∨ ((((p1 → ((p3 → True) → True)) → ((True ∧ p5) ∧ (False → p2))) ∨ ((p1 → p4) ∧ p3)) ∨ (p1 → ((p2 ∨ p1) → True))))) := by
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
theorem thm_5_vars_668050296811968992156911397449 : ((((p5 ∨ ((((p4 ∨ False) → p1) → p4) ∨ (p4 ∨ (p4 → (p3 ∨ ((True → p2) ∨ ((True ∧ p4) → False))))))) ∧ ((p3 → p2) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762598726030113160005659059449 : (((p3 ∧ (((False ∧ False) ∨ ((((p2 ∧ (p3 ∨ p5)) ∧ p5) → (False ∧ p1)) → p3)) ∧ ((p4 ∨ p2) ∨ (p1 ∨ (False ∧ (p1 ∨ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166390957005123772681694147717 : ((False ∨ (((p5 → p2) → (p4 ∨ False)) ∨ (p5 ∨ (((p5 → (True ∨ p1)) → p4) ∧ p4)))) ∨ (((p2 ∨ ((p4 → p4) ∧ p1)) ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258724539453177969383503728531 : ((True → True) → (((True → ((True ∧ ((False ∧ ((p5 ∧ p2) ∨ True)) ∧ True)) ∨ p3)) ∧ p1) → ((((p4 ∨ True) → p2) ∧ p2) ∨ (p3 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117356660187785656998421116531 : ((False ∧ (p5 ∧ (((p1 ∧ ((p1 ∨ (p5 ∨ False)) ∨ p4)) → p5) ∧ (True → ((p2 ∧ (((p4 ∨ True) → p3) ∧ p3)) ∨ True))))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299109672532673409984274901763 : (False ∨ (((True ∧ ((((True ∧ ((p1 ∨ (True ∧ p2)) → True)) ∧ p5) ∧ ((p4 ∧ p3) ∧ p3)) ∧ ((p5 → p3) → (p4 → False)))) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111224185737584253587840697926 : ((((p1 → (p4 ∧ p3)) → (p2 ∨ ((((((p4 ∨ ((p1 ∨ p1) → p3)) ∧ p5) → (p4 ∧ p1)) ∧ p2) → p1) ∨ False))) ∧ p4) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204804965549796134992448872146 : (((((p1 → p2) ∧ p2) ∨ False) → p3) ∨ (p3 ∨ ((p2 → ((((p1 → p5) ∨ p1) → False) ∨ ((p1 → (p2 ∨ False)) ∨ (p3 → p5)))) ∨ p1))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617945971917675198133162640975 : (((((p5 ∨ ((p4 ∧ (p3 → p1)) ∨ p2)) → ((p5 ∧ p1) ∨ ((p2 → ((True → True) → (p1 ∧ p4))) ∨ ((p2 ∨ False) → True)))) ∨ p4) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141815779141070793331401545535 : (((p4 ∧ p5) ∨ ((p5 → (p2 ∧ ((True ∨ p3) → False))) ∧ ((p2 ∨ ((p1 → (p3 ∨ p1)) ∨ p3)) ∧ (p2 ∧ True)))) → (p1 ∨ (p3 ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h9.left
        let h16 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h9.left
        let h19 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323831647068304763173407022375 : (p5 ∨ ((((p5 → (p1 → (p4 → (p1 ∧ p3)))) → False) ∧ (p4 → ((False ∧ (p4 → p2)) ∧ False))) → ((p3 → ((p5 → p1) ∨ True)) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : (p5 → (p1 → (p4 → (p1 ∧ p3)))) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h9
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h11 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h12 := h6 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h14 := h5 h7
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137144514639689405139078851878 : ((True ∧ (p3 → (((((((p3 ∧ True) → p2) ∨ (p4 ∧ (True ∨ p1))) ∧ (p1 → (False → False))) ∧ p5) → p4) → False))) ∨ ((False ∧ p1) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175570100045673151703613209456 : ((p5 → (p4 ∧ ((p1 → ((p3 ∧ p3) → ((p4 → p1) ∧ (p1 ∨ False)))) → False))) → (p2 ∨ (p4 ∨ (((True → p4) ∧ (p5 ∧ p3)) → p2)))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : (p1 → ((p3 ∧ p3) → ((p4 → p1) ∧ (p1 ∨ False)))) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h11
    -- Conjunctions on the left can always be decomposed.
    let h16 := h12.left
    let h17 := h12.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h18 := h9 h10
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788498662370112348541268491837 : (((p5 ∨ ((p3 ∧ (((((p4 → True) → (p3 ∨ p4)) ∧ p3) ∧ p2) ∧ (False → ((p4 ∨ (p4 ∨ p3)) ∧ ((p1 → p4) ∨ p4))))) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_192167971295115071991143005142 : ((((False ∨ (False → ((p1 → False) ∨ True))) ∧ p1) ∧ p1) → ((((True ∧ False) ∨ (True → p3)) ∧ (p2 ∨ ((p4 ∨ True) → p2))) ∨ (True ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
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
theorem thm_5_vars_158551149683167819170386703058 : (((p5 → False) → (p3 → ((p3 → False) ∨ ((((p5 → p2) ∧ p5) ∧ p1) ∧ (p5 ∧ (p3 ∧ p1)))))) ∨ (((p5 → (p4 → p4)) → False) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → (p4 → p4)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756645565355818810030945311621 : (((p1 ∧ (((False → (True → True)) ∧ ((False ∧ (p2 ∨ (p4 ∨ p3))) ∧ (p1 ∧ p1))) ∧ (True ∨ (p4 ∧ (p3 → ((False ∧ p4) ∨ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164925716060596605139908500314 : ((((((False ∨ p3) ∧ (((False → p3) → (p5 ∨ p1)) → p3)) → (False ∧ False)) ∨ p4) → p1) ∨ (p3 ∨ (p3 → (p3 → (p3 ∧ (p3 ∨ p3)))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177261164106005814805573531014 : ((False ∨ (((p2 ∧ False) ∨ False) → (((False → True) ∨ (True → True)) ∧ p5))) ∧ (((True ∧ p5) → ((False ∧ p2) ∧ p2)) ∨ (False → (p3 → p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330723662584294199828519605449 : (True → (p1 → ((p3 ∧ ((((p1 → (p2 ∨ ((p1 ∧ (p5 ∧ p3)) ∧ ((p4 → p4) ∧ (p4 ∧ p4))))) ∨ p1) ∧ (p3 ∧ False)) ∧ True)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644182676459645937153983812635 : ((((True ∨ (p2 → (p2 → (p1 ∨ ((((p5 → p4) → (p5 ∧ (((p5 ∨ True) ∨ p1) ∧ ((p3 ∧ True) ∨ p4)))) ∧ p5) → p2))))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53065904191614906849834123190 : (((False ∧ ((p4 ∨ (p1 → False)) → ((True ∨ (p1 → True)) → p5))) ∧ (p2 → (((p1 ∨ p1) ∨ (p3 ∨ ((p3 → False) ∨ p1))) → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137749425220182055075519706857 : ((p2 ∨ (((p2 ∧ (p5 ∨ (((True ∨ (((True ∨ True) → True) ∨ p2)) ∧ False) ∧ (p4 → (p1 ∨ False))))) ∨ p3) ∨ p1)) ∨ ((p5 ∨ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313365323252643751918837444485 : (p3 ∨ ((p4 → (((((p4 ∨ (p1 ∧ p5)) ∨ True) ∧ (p2 ∨ ((p1 → (((False ∧ p3) ∨ p1) → True)) ∧ p4))) ∧ (p2 ∧ p2)) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226184833770675439818815063407 : (((p1 ∨ p4) ∨ p5) ∨ ((((((True → p3) → p5) ∨ p2) ∨ ((p2 ∨ False) → p1)) → p3) → (((False ∨ p4) ∧ (p5 ∧ p4)) ∨ (p4 ∨ True)))) := by
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
theorem thm_5_vars_200240288164972417841091239755 : ((((False ∧ p3) → p2) → (p2 → (p2 ∧ p1))) → ((p3 ∧ p4) ∨ ((p3 → p1) → (p2 ∨ (p3 ∨ (((p3 ∧ (p1 ∨ p5)) ∨ p3) → p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h9 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h9
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h12
    -- One of the premise coincides with the conclusion.
    exact h13



