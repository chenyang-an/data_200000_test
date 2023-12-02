variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623812646013510746826356419831 : ((((p1 ∨ (((p4 ∨ p4) ∨ p2) → (((True → (False ∧ (((p2 → p3) ∨ (p1 ∨ p2)) ∨ ((p4 ∨ p3) ∧ False)))) ∨ p1) ∨ True))) ∨ p4) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164657009775467546164539886744 : (((p2 → ((True ∨ True) ∧ (((False ∧ p3) → (True → (p1 ∧ p1))) → (False ∧ False)))) ∧ False) ∨ (p3 → (((True → p3) ∨ p1) ∨ (p1 ∨ p2)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615345353573512569718355379280 : ((((((((p4 ∨ (True ∧ p2)) ∧ (False ∧ False)) ∧ p3) ∧ ((False ∨ (p1 ∧ p1)) → p4)) ∨ ((p3 ∨ (p3 → (p5 → p2))) ∨ True)) ∨ False) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_342916152469650855423724945047 : (p2 → ((p2 → ((False ∧ p2) → (p2 ∧ p5))) → ((((p1 → (((((p1 ∨ True) → p3) ∧ True) → False) ∨ True)) ∨ (p1 → p1)) ∨ True) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67571395208719249876716994841 : ((p1 → ((False ∨ p5) ∨ ((p4 → p2) → ((p4 → (True ∨ (p3 ∧ p5))) ∧ (p3 ∨ (((p2 ∨ ((True ∧ p2) ∨ p1)) → p3) → p3)))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p2 ∨ ((True ∧ p2) ∨ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339039081348254168813857098896 : (p1 → (True ∧ (False ∨ (p2 ∨ ((True ∧ (((False → ((p2 → p4) ∨ (((p4 ∧ p5) → p3) ∧ p5))) → False) ∨ (p1 ∨ (True ∨ p3)))) ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309918953454643165573593965588 : (p2 ∨ ((((p5 → (p4 ∨ ((p2 ∨ p5) → False))) → ((p1 ∨ (p5 ∨ p1)) ∧ p5)) ∧ (True ∧ True)) ∨ (((p3 → (p3 ∨ p1)) ∧ True) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64936081506993816562733206574 : ((p2 ∨ (((p4 ∨ (p1 → (p2 ∨ p1))) ∧ (p2 ∧ ((p5 ∧ p1) ∨ False))) ∧ ((p1 ∧ True) ∨ ((p1 ∨ ((True ∨ p1) ∧ False)) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47191514812790547899530640765 : (((((((p2 ∨ p5) → (((p2 ∧ True) ∨ p3) ∧ p5)) ∨ p2) → p3) ∨ (p2 ∨ ((p3 ∨ p3) ∨ (True ∨ (p4 → p5))))) ∨ (p5 ∨ p1)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124545896744768588817643086156 : (((p1 → (((True ∨ p4) ∧ p4) → p2)) ∧ (False → (p3 ∧ ((True ∧ p4) ∧ ((p3 → (True → p4)) → ((p3 → p5) ∨ True)))))) → (p5 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107313648811821263159453652176 : ((((p1 ∨ p3) → False) ∨ (((p2 ∨ True) → (p1 ∨ p2)) ∨ (p4 ∨ ((p2 ∨ ((((p1 ∧ p3) → p3) ∧ p3) ∧ p4)) → True)))) ∧ (p2 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700778021831471816817206610660 : ((((((p1 ∧ (True → p3)) ∨ ((p3 ∨ True) → False)) ∧ True) ∧ ((p4 → ((False → (p1 ∨ True)) → (p3 ∨ (p4 ∧ p5)))) ∧ (p4 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230344826895453400063656430099 : (((p2 ∨ p2) ∧ p4) → ((((((p2 ∧ (((True ∨ False) ∧ ((p4 → (p2 → (p5 → p5))) ∨ p2)) → p3)) ∧ p4) → p5) ∨ p5) ∧ False) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160091168499501222679778771132 : (((p4 ∨ (((p4 ∨ (((p5 → p3) ∧ ((p5 ∨ p2) ∨ (p2 ∨ True))) → True)) ∨ p4) ∧ False)) → p1) → ((p5 ∨ ((False ∨ p1) ∨ True)) ∨ p2)) := by
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
theorem thm_5_vars_155607223966345236985985729087 : (((True ∨ p4) ∧ ((((((False ∨ (True ∧ p3)) → p4) ∨ (p2 ∧ p2)) ∨ (p1 → p4)) ∧ p2) ∨ True)) ∧ ((False → True) ∨ ((True ∨ p5) → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352809590629781918692144690834 : (p4 → ((p4 ∨ p2) → ((p1 ∧ p3) ∨ ((False ∧ p3) ∨ (((p5 ∧ ((((True ∨ p1) ∨ (True → False)) ∧ p1) → (True ∨ p5))) ∧ p5) → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312090937326286247366839707751 : (p2 ∨ (p5 ∨ (p1 ∨ ((True ∧ p1) ∨ (p3 ∨ (((False → p5) ∨ ((p1 → (True → p5)) → (p1 ∨ p4))) → ((True ∨ True) ∧ (True ∨ p1)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65006811880245084513290468968 : ((p2 ∨ ((p2 ∧ p1) ∧ (False ∨ (((True → (p2 ∧ (False → p1))) ∨ p3) → ((p3 ∨ p3) ∧ (p3 ∧ (p3 → ((p5 ∧ p3) ∧ p1)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213989095030508331522425532839 : (((p5 → (p4 ∨ p4)) ∨ False) ∨ ((p1 ∧ (((False → (p1 → (p5 ∨ (False ∧ p3)))) ∨ p4) ∧ (p2 ∧ p1))) → (p5 ∨ ((True ∨ p3) → p1)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h5.left
    let h14 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263608543271355541987259628208 : (True ∧ ((((True ∧ p4) → ((((False ∨ False) ∨ (((p3 → False) ∨ False) → True)) ∨ True) ∨ p5)) ∨ (False ∨ False)) → ((p3 → (p4 ∧ False)) ∨ True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737222515899621276448802888842 : ((((p4 → True) ∧ ((p2 → ((p3 → True) ∧ p4)) ∧ ((((((True ∨ p1) ∧ (p1 ∧ p4)) → (p4 ∨ p4)) → (p2 ∨ p4)) ∨ p3) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260913412468211232560073645032 : ((p4 → False) → ((((((p4 ∧ False) ∨ p5) ∨ (True ∧ False)) ∧ False) ∨ True) → ((((p5 → p1) ∧ p4) → ((False ∧ p3) ∧ p4)) ∨ (p4 ∨ False)))) := by
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
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h5
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h18 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h19 := h1 h18
    -- False on the left can always be used.
    apply False.elim h19
    -- Conjunctions on the left can always be decomposed.
    let h20 := h15.left
    let h21 := h15.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h22 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h21
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h23 := h1 h22
    -- False on the left can always be used.
    apply False.elim h23
    -- Conjunctions on the left can always be decomposed.
    let h24 := h15.left
    let h25 := h15.right
    -- One of the premise coincides with the conclusion.
    exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51143509782958249778843771327 : (((((((p5 → p4) ∧ p2) ∨ ((((p3 ∨ p3) ∨ p3) → p1) ∧ False)) ∨ (True ∨ p1)) → p5) ∨ (True ∨ (((True → p3) ∧ p2) → p4))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136736867130968008714078064197 : (((True ∨ p4) ∧ ((((p5 ∧ p2) ∨ (((False → (p2 ∧ p3)) ∧ p2) → p1)) → p4) → ((p3 ∧ True) → (p3 → p3)))) ∨ ((p3 ∨ False) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302791603296874113842082807071 : (False ∨ (p4 ∨ (p3 → (p5 → (((((True → (((p3 → (p3 ∧ p1)) ∨ (p4 ∧ p4)) ∨ False)) ∨ p5) → False) ∧ p5) → ((p3 → p2) ∨ p3)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216925236722764018397887918136 : (((True → (True ∧ False)) ∧ p5) → ((((p2 ∨ (True ∨ (p2 ∨ p3))) → (p5 ∧ (((p4 ∧ (p3 → p3)) ∨ (p4 ∨ True)) → p3))) ∧ True) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h1.left
      let h9 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h1.left
        let h13 := h1.right
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h1.left
        let h16 := h1.right
        -- One of the premise coincides with the conclusion.
        exact h16
  -- Implications on the right can always be decomposed.
  intro h17
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h1.left
      let h23 := h1.right
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h24 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h25 := h22 h24
      -- We need to get the right conjuct of h25 based on <expert-advice>.
      let h26 := h25.right
      -- False on the left can always be used.
      apply False.elim h26
    case inr h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- Conjunctions on the left can always be decomposed.
        let h29 := h1.left
        let h30 := h1.right
        -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
        have h31 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h29, we can now drive its conclusion.
        let h32 := h29 h31
        -- We need to get the right conjuct of h32 based on <expert-advice>.
        let h33 := h32.right
        -- False on the left can always be used.
        apply False.elim h33
      case inr h34 =>
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h35 =>
          -- Conjunctions on the left can always be decomposed.
          let h36 := h1.left
          let h37 := h1.right
          -- We want to use the implication h36 based on <expert-advice>. So we show its premise.
          have h38 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h36, we can now drive its conclusion.
          let h39 := h36 h38
          -- We need to get the right conjuct of h39 based on <expert-advice>.
          let h40 := h39.right
          -- False on the left can always be used.
          apply False.elim h40
        case inr h41 =>
          -- Conjunctions on the left can always be decomposed.
          let h42 := h1.left
          let h43 := h1.right
          -- One of the premise coincides with the conclusion.
          exact h41
  case inr h44 =>
    -- Disjunctions on the left can always be decomposed.
    cases h44
    case inl h45 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h46 =>
        -- Conjunctions on the left can always be decomposed.
        let h47 := h1.left
        let h48 := h1.right
        -- We want to use the implication h47 based on <expert-advice>. So we show its premise.
        have h49 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h47, we can now drive its conclusion.
        let h50 := h47 h49
        -- We need to get the right conjuct of h50 based on <expert-advice>.
        let h51 := h50.right
        -- False on the left can always be used.
        apply False.elim h51
      case inr h52 =>
        -- Disjunctions on the left can always be decomposed.
        cases h52
        case inl h53 =>
          -- Conjunctions on the left can always be decomposed.
          let h54 := h1.left
          let h55 := h1.right
          -- We want to use the implication h54 based on <expert-advice>. So we show its premise.
          have h56 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h54, we can now drive its conclusion.
          let h57 := h54 h56
          -- We need to get the right conjuct of h57 based on <expert-advice>.
          let h58 := h57.right
          -- False on the left can always be used.
          apply False.elim h58
        case inr h59 =>
          -- Disjunctions on the left can always be decomposed.
          cases h59
          case inl h60 =>
            -- Conjunctions on the left can always be decomposed.
            let h61 := h1.left
            let h62 := h1.right
            -- We want to use the implication h61 based on <expert-advice>. So we show its premise.
            have h63 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h61, we can now drive its conclusion.
            let h64 := h61 h63
            -- We need to get the right conjuct of h64 based on <expert-advice>.
            let h65 := h64.right
            -- False on the left can always be used.
            apply False.elim h65
          case inr h66 =>
            -- Conjunctions on the left can always be decomposed.
            let h67 := h1.left
            let h68 := h1.right
            -- One of the premise coincides with the conclusion.
            exact h66
    case inr h69 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h70 =>
        -- Conjunctions on the left can always be decomposed.
        let h71 := h1.left
        let h72 := h1.right
        -- We want to use the implication h71 based on <expert-advice>. So we show its premise.
        have h73 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h71, we can now drive its conclusion.
        let h74 := h71 h73
        -- We need to get the right conjuct of h74 based on <expert-advice>.
        let h75 := h74.right
        -- False on the left can always be used.
        apply False.elim h75
      case inr h76 =>
        -- Disjunctions on the left can always be decomposed.
        cases h76
        case inl h77 =>
          -- Conjunctions on the left can always be decomposed.
          let h78 := h1.left
          let h79 := h1.right
          -- We want to use the implication h78 based on <expert-advice>. So we show its premise.
          have h80 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h78, we can now drive its conclusion.
          let h81 := h78 h80
          -- We need to get the right conjuct of h81 based on <expert-advice>.
          let h82 := h81.right
          -- False on the left can always be used.
          apply False.elim h82
        case inr h83 =>
          -- Disjunctions on the left can always be decomposed.
          cases h83
          case inl h84 =>
            -- Conjunctions on the left can always be decomposed.
            let h85 := h1.left
            let h86 := h1.right
            -- We want to use the implication h85 based on <expert-advice>. So we show its premise.
            have h87 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h85, we can now drive its conclusion.
            let h88 := h85 h87
            -- We need to get the right conjuct of h88 based on <expert-advice>.
            let h89 := h88.right
            -- False on the left can always be used.
            apply False.elim h89
          case inr h90 =>
            -- Conjunctions on the left can always be decomposed.
            let h91 := h1.left
            let h92 := h1.right
            -- One of the premise coincides with the conclusion.
            exact h90
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h93 := h1.left
  let h94 := h1.right
  -- We want to use the implication h93 based on <expert-advice>. So we show its premise.
  have h95 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h93, we can now drive its conclusion.
  let h96 := h93 h95
  -- We need to get the right conjuct of h96 based on <expert-advice>.
  let h97 := h96.right
  -- False on the left can always be used.
  apply False.elim h97



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157115587479968981916506128172 : (((((((False ∨ (((True ∧ p2) ∨ True) ∨ p4)) ∧ (p4 → p2)) ∨ (p1 → True)) ∧ p1) ∧ p5) → p4) ∨ (False → (((p5 → p2) → p3) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356535775043684885462751110334 : (p5 → (((p2 ∨ False) ∧ (True → (((False ∧ p3) → p3) ∧ p3))) ∨ (p2 ∨ ((((False → p4) ∨ (False ∧ (False ∧ (p5 ∧ p1)))) → p2) ∨ True)))) := by
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
theorem thm_5_vars_329008790429633580649581785744 : (True → ((p1 → ((p2 ∧ (True ∨ p2)) ∨ p4)) ∨ (p2 → ((((p3 ∨ (p3 → False)) ∨ True) → (True ∧ (p4 ∧ False))) ∨ (True ∨ (True ∨ p2)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167234007242696421978105833818 : (((p1 → (((p2 → p4) ∨ (p5 ∧ ((p3 → True) ∧ (False ∨ (p5 ∧ p5))))) ∧ p1)) ∨ p5) → (((True → p3) ∨ (True ∧ (True ∧ True))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687311648315171562689688028956 : ((((((p5 ∨ (False ∧ p5)) → ((((p4 → True) ∧ p3) → (p5 → False)) → True)) ∧ p5) ∧ (((p2 ∧ p1) → (p4 → (False ∨ False))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358573086378789080885690767640 : (p5 → (p2 → (p5 → ((p2 ∧ ((p1 ∧ p4) → p4)) ∧ ((p5 ∧ ((((p5 ∨ p5) → p1) ∧ p1) ∧ p4)) ∨ (False ∨ ((p4 ∧ False) → False))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157359331216129449847537207612 : (((p1 → ((p4 ∧ (p5 → ((p3 ∧ (p2 ∨ True)) ∨ (p5 ∨ ((p5 → True) ∧ p4))))) → p5)) → p2) ∨ ((False → p1) → (p2 → (p2 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90773287586430346064960979661 : (((p2 ∨ p2) ∧ (((p1 ∨ ((p4 → (p4 ∧ ((p4 ∧ p2) → (p5 → False)))) → (p1 ∨ True))) ∨ (False ∨ (p1 → (True → p5)))) → False)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : ((p1 ∨ ((p4 → (p4 ∧ ((p4 ∧ p2) → (p5 → False)))) → (p1 ∨ True))) ∨ (False ∨ (p1 → (True → p5)))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h5
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : ((p1 ∨ ((p4 → (p4 ∧ ((p4 ∧ p2) → (p5 → False)))) → (p1 ∨ True))) ∨ (False ∨ (p1 → (True → p5)))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h9
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40597693470776947919487942029 : (((((p3 → (p4 ∧ ((p3 ∧ ((p5 → False) ∧ p4)) ∨ (p4 ∨ (((p1 ∨ ((p1 ∧ p2) ∧ p4)) ∧ p2) ∨ p2))))) ∧ p3) → p1) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747486193391703549610828171933 : ((((True → p1) → (((p1 → p1) → (p3 → ((p4 ∧ p5) ∨ ((p1 → (((p1 ∨ p1) ∧ p4) → (p2 ∨ p2))) ∨ p1)))) ∨ (p5 ∧ p1))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322472789398671001988649046792 : (p5 ∨ (((p3 ∧ p4) ∧ ((p4 ∨ (True ∧ (p4 ∨ ((((False ∨ (((p4 → p3) → True) → (p2 ∧ p3))) → p4) ∧ p1) → p1)))) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198684444131332198631273160935 : ((p4 ∨ ((False ∨ p2) ∨ ((False ∨ p5) ∧ False))) ∨ ((p5 ∧ (True ∨ (False ∧ p5))) → (True ∨ (p5 ∨ (((True ∨ p2) ∧ p2) ∧ (p4 ∨ False)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191531233935085197890197150296 : ((p1 ∧ (((((p2 ∨ p1) → p1) ∧ p3) ∧ p5) ∧ p2)) ∨ (p4 → ((((p2 ∨ p5) ∧ ((False ∨ True) ∨ p3)) → ((p1 ∧ True) ∧ False)) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58903070921016729254741142018 : (((False ∧ p5) ∨ (((p3 ∧ (p2 ∨ p4)) ∨ False) ∧ (((((True ∨ False) → p3) ∨ p4) ∧ p3) ∧ (((p3 → p1) ∧ p3) → (True ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618738087038625766539610196648 : ((((((p4 ∧ p1) → False) ∧ (True ∧ (p2 → ((((p1 → p2) → (p1 ∨ p5)) ∨ p3) → (((p1 ∧ p4) ∧ (False ∧ p5)) ∧ p2))))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_143784323827567260898219714149 : ((((p5 ∨ (p4 → (((p4 ∨ p5) ∧ (p1 ∧ ((p2 → p5) ∧ (p2 ∨ False)))) ∧ (p1 ∧ p3)))) ∧ p5) ∨ True) ∧ (((True ∨ p4) → p4) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178236379819642741168220295514 : (((p5 → ((((True ∨ p5) ∨ p2) ∧ ((False ∧ p2) → True)) ∨ p1)) → p3) ∨ (((((((p5 → p1) → p5) ∨ p1) → p5) ∨ p3) ∨ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356381664080294034760523822854 : (p5 → ((((p3 ∧ p2) → ((False ∧ (p4 ∨ True)) → (p4 ∧ p5))) → (p4 ∧ p3)) → ((p2 ∧ False) ∨ ((p5 ∨ (p5 ∧ (False ∧ p5))) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p3 ∧ p2) → ((False ∧ (p4 ∨ True)) → (p4 ∧ p5))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
    -- Conjunctions on the left can always be decomposed.
    let h8 := h5.left
    let h9 := h5.right
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h3
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340891545464343348661679077550 : (p2 → (((False ∨ (p4 → (((p3 ∨ (((p4 ∨ p5) ∧ True) ∨ p5)) ∧ p1) ∧ p1))) → (((p5 ∧ ((True → p1) → False)) ∨ True) ∨ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607834714977734495108195877231 : (((((p4 ∨ (p2 ∨ (p4 ∨ ((p5 → (p1 ∨ ((p5 ∨ (False ∨ p5)) ∧ p5))) → ((((p3 ∨ False) → p4) ∨ p2) ∨ True))))) ∧ True) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59322390343766548459766749009 : (((p4 ∨ p3) ∨ ((((p4 ∧ (p4 → (((True ∧ (p2 ∧ True)) → p1) ∨ False))) ∨ p4) ∨ (((p3 ∧ (p1 ∧ p4)) → p3) ∧ p3)) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172095035456868061182917235560 : (((p2 ∧ ((True ∧ ((p3 ∨ p3) → (p5 ∧ (p2 ∨ p1)))) → p5)) → (False ∧ p3)) ∨ (((p3 ∨ p1) → (p1 → p1)) ∨ ((p3 → p1) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618020286604331226585069816814 : ((((((p2 ∨ (p4 ∨ False)) ∨ True) ∧ (True ∧ ((p5 ∨ p5) → (((True ∨ p2) → (((p5 ∧ True) ∧ p2) ∨ p4)) → (True → p3))))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_27848022683110400535629986849 : (((True → True) → (p3 ∨ (((p2 ∨ (((True ∧ (p5 ∨ p2)) → False) → (p2 ∧ (p4 → False)))) ∨ ((False → p4) → True)) ∨ (p1 ∨ p5)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116493914507325711862568824353 : (((p3 ∧ True) ∧ ((p3 ∨ (False ∧ (p3 ∨ (p3 ∨ p2)))) ∨ ((True → (((False ∧ p2) → p3) ∧ (False ∨ (p1 ∧ p1)))) ∧ p2))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9756836017956944110881237628 : ((((p5 ∧ p3) → ((p3 ∨ True) ∧ (p3 ∧ ((True → (((False → (p5 ∨ False)) → (False ∧ (False ∧ (False → p1)))) ∨ p5)) ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157299862711172014757704667388 : ((((p3 → p4) → (((True ∧ False) ∨ False) ∨ ((p3 ∨ (p2 ∨ ((p5 ∨ p2) → False))) → False))) → p2) ∨ (((p3 ∨ (p3 ∧ p1)) → True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337679679608425088442983190816 : (p1 → ((True → (((p1 ∧ (((True ∨ True) → (p3 ∨ p4)) ∨ p2)) → ((p2 ∧ p2) → p4)) ∧ True)) ∨ ((((p1 → False) ∨ p1) ∧ p4) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226504661410549011664492142538 : (((p2 → p5) ∨ p4) ∨ ((p5 ∨ (p1 ∨ p5)) ∨ ((p2 ∧ (p5 ∨ (((p2 ∨ p1) ∨ (p4 ∧ p2)) ∨ (p1 → p3)))) → ((p4 ∧ p5) ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
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
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323598846010256293573864338717 : (p5 ∨ ((p5 → ((p2 ∨ (p4 ∨ p1)) ∧ ((p5 ∨ ((p4 ∨ ((p2 → p5) ∨ (p2 ∧ True))) → (p3 ∧ p1))) ∧ False))) → ((True → p5) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66225316161592874795507211311 : ((p5 ∨ (((((p1 ∧ True) ∧ (p2 → (True ∨ p3))) ∨ p2) ∨ p1) → (p2 ∧ ((False → (p5 ∧ (p5 ∨ p3))) → ((p1 → p3) → p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157996755402459418555054353126 : ((((True → True) → (((p4 ∧ p3) ∧ p5) ∧ True)) → (p1 ∧ (p2 ∧ (p2 → ((p3 → False) ∨ p4))))) ∨ ((((p1 ∧ p1) → p1) ∧ p3) → p3)) := by
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
theorem thm_5_vars_748866136714314339038780676074 : ((((p4 → p1) → ((((False ∨ p3) → p3) ∧ (p4 ∨ (p5 ∨ (((p4 ∧ ((p4 ∨ p2) ∨ False)) ∧ p5) ∧ True)))) ∨ (p2 → (p3 → True)))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_171770629557351080417537101944 : ((((p4 ∧ ((p3 ∨ p2) → ((((p2 ∨ p2) ∨ p2) → p4) → True))) → p1) → p3) ∨ (False ∨ (p3 ∨ (p4 → (((p1 ∨ p2) ∧ False) → False))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229555262174197290842170224933 : ((p2 → (p2 → p1)) ∨ ((((True → (((p4 → (True ∧ ((p1 ∨ p2) → (p3 ∧ p5)))) ∨ ((p2 ∧ True) ∧ p5)) ∧ p3)) ∧ p1) ∨ False) → p3)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115138680641270067444165107124 : ((((p5 ∧ p3) → ((((p4 → (p1 → False)) ∧ False) → p5) ∨ p5)) → ((p3 → p2) → ((((p3 → p3) → p5) ∨ False) ∨ p2))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779135929586726824080615581753 : (((p2 ∨ ((((((((p1 ∧ (p2 ∧ (p4 → p2))) ∧ False) ∧ p5) ∧ p4) ∨ ((p3 ∧ p3) → ((p1 → p1) ∧ p3))) ∨ p3) → p4) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55986895388116252875106651061 : ((((True ∨ (False ∨ False)) ∧ p4) ∨ (((p5 → (False ∧ (p4 → p1))) → (((p5 ∧ (p1 ∨ False)) → ((True ∨ p1) ∨ True)) → False)) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316510369464487475553853099923 : (p3 ∨ (p2 ∨ (((True → False) ∧ (((False → False) ∨ ((p2 → p2) → p4)) ∧ p2)) → ((p4 → (p1 ∧ p1)) ∧ (True ∧ (p1 ∨ (False ∧ False))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- False on the left can always be used.
    apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h14.left
  let h16 := h14.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h17 =>
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h18 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h19 := h13 h18
    -- False on the left can always be used.
    apply False.elim h19
  case inr h20 =>
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h21 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h22 := h13 h21
    -- False on the left can always be used.
    apply False.elim h22
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h23 := h1.left
  let h24 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h25 := h24.left
  let h26 := h24.right
  -- Disjunctions on the left can always be decomposed.
  cases h25
  case inl h27 =>
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h28 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h29 := h23 h28
    -- False on the left can always be used.
    apply False.elim h29
  case inr h30 =>
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h31 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h32 := h23 h31
    -- False on the left can always be used.
    apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112979089765629097905792145149 : (((p2 ∧ ((p2 ∧ ((p1 ∨ p4) ∧ (False → ((p5 ∨ ((p4 ∧ (True → (p5 → True))) → (True → p5))) → p3)))) ∨ False)) → p3) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717817747359357614199738751355 : ((((((p5 → p5) → False) ∧ p2) ∨ ((((p2 ∧ ((p4 ∨ p3) ∧ (((p5 → ((p2 ∨ p1) ∨ p5)) → p3) ∨ p5))) → p2) → p2) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588412291912182918478744375839 : ((((((False ∨ (p4 → False)) ∨ ((p4 ∧ (((((p3 ∧ (p1 → False)) → p4) ∨ (p3 → p2)) ∧ (p4 → p5)) → p5)) ∧ False)) ∨ p5) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161447305182223178979658111051 : ((p2 ∧ (True → (p1 → ((p3 ∨ (p2 ∧ (((p4 ∧ ((True → p2) ∨ True)) → False) ∧ p1))) ∨ p2)))) → (p5 → (((p1 → p4) ∧ p5) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49833534290015533962665464557 : (((p4 → ((p4 ∧ p5) → (p3 → ((((((p2 → p1) → True) → (True ∧ p3)) → False) ∨ (p4 ∨ p5)) ∧ False)))) → ((p5 ∧ True) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776094611855014863348706601196 : (((False ∨ (p5 → (True ∧ (False ∨ ((True ∧ False) ∨ (((p1 ∧ ((False ∨ p4) ∧ p3)) ∧ ((p2 → (p1 ∨ (True ∧ True))) → p4)) ∨ True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175350439085057466455172308823 : ((p5 ∨ (((p4 ∨ (False ∧ (p4 → False))) ∨ p5) ∧ ((p5 → (p5 ∨ True)) ∧ p2))) → ((p2 ∨ ((p3 ∧ p1) → (p1 → p2))) → (p3 ∨ True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h7.left
          let h11 := h7.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- False on the left can always be used.
          apply False.elim h13
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h7.left
        let h17 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h22.left
          let h26 := h22.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h27 =>
          -- Conjunctions on the left can always be decomposed.
          let h28 := h27.left
          let h29 := h27.right
          -- False on the left can always be used.
          apply False.elim h28
      case inr h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h22.left
        let h32 := h22.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172450569882534824838662822107 : ((((False ∨ True) ∧ (p3 ∧ p5)) ∨ ((True → ((True ∧ (True ∨ p3)) ∧ False)) ∨ p2)) ∨ ((False → False) ∨ (p5 → (p2 ∧ ((p1 → False) → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115026165627370387312304745888 : (((p5 ∨ ((True → (p5 → (p5 ∨ ((p4 → True) ∨ False)))) ∧ p4)) ∧ ((p3 → (p1 ∨ p2)) ∧ (((False ∧ p5) ∨ p4) → p1))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621067373727575150455007518149 : (((((p2 → p1) → (p4 → (((p3 → ((p1 ∧ p4) ∨ False)) ∧ ((p3 ∨ (p2 ∧ (p2 ∨ p3))) ∧ (p2 ∧ (p3 ∧ p1)))) ∨ False))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_156622741494884032210439594273 : ((((((((p5 ∧ p2) ∧ ((False ∧ p5) ∨ p5)) ∨ False) → ((p2 ∨ False) ∨ p5)) → p1) ∨ p2) ∧ p1) ∨ (((p5 ∧ (p2 ∧ True)) ∧ p3) → p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45628209722078089607570625507 : (((p4 ∨ (((p3 → ((p1 ∨ (p1 ∧ (p1 → False))) ∧ False)) → (((p3 ∧ (p2 ∨ False)) → p4) ∨ (p5 ∧ (p3 ∧ False)))) → p5)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142990923973445251827446132299 : ((True → (((p4 ∧ p3) ∧ (((p4 ∨ p4) ∨ p2) ∨ ((p3 ∧ ((True ∧ p4) ∨ p1)) ∨ p4))) ∧ ((p4 ∧ False) ∧ True))) → ((True → False) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_975981927212848864436512431432 : (((True ∧ ((((p1 ∨ True) ∧ ((p2 ∧ (((p5 ∨ p5) ∨ p2) ∨ p4)) → False)) ∧ ((p4 → (True → False)) ∧ ((p1 → p3) ∧ p4))) ∧ p3)) → p5) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h7.left
    let h12 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h15 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h16 := h11 h15
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h17 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h18 := h16 h17
    -- False on the left can always be used.
    apply False.elim h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h7.left
    let h21 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h24 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h23
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h25 := h20 h24
    -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
    have h26 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h25, we can now drive its conclusion.
    let h27 := h25 h26
    -- False on the left can always be used.
    apply False.elim h27
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217099899504763467300502052449 : ((((p4 ∧ p3) ∨ True) ∨ p2) → ((((((True ∨ False) → (False ∨ p2)) ∨ (p5 ∧ (p4 ∨ (p5 → p2)))) ∧ p5) ∨ (p1 → p2)) ∨ (p1 ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
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
theorem thm_5_vars_59971617635013436272909278660 : (((False ∨ True) → ((p5 ∧ (True ∨ (True ∧ True))) → (p5 → (((p1 ∧ p2) ∨ ((p2 ∧ p1) → (False ∧ ((False ∨ False) → False)))) ∨ p5)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133910179821895551777185759559 : (((p2 ∨ (p1 → (((p2 → p2) → ((p5 → ((True ∨ p5) → p3)) → False)) ∨ (False ∨ (False ∨ (p5 ∨ True)))))) ∧ p3) ∨ (p1 → (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740088133925991816365087869755 : ((((False ∨ p2) ∨ (((((p2 ∧ (True ∨ False)) ∧ p5) ∨ (((True ∨ (False ∨ False)) ∨ (p4 ∨ p4)) → True)) ∧ False) ∨ (p2 ∨ (False → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346922020686931022554374759053 : (p3 → ((p5 ∧ (p2 ∧ (p3 ∧ ((p3 ∨ (((p5 ∧ (False → (p5 ∧ p5))) ∨ p1) → p2)) → False)))) ∨ (p4 → (True ∨ ((p5 → p1) ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300770804750807641958928188276 : (False ∨ ((((p3 ∨ False) ∨ ((p3 ∨ (((p2 ∧ True) ∨ (p2 ∨ True)) → p3)) ∧ p2)) ∧ p3) ∨ ((p4 → ((True ∧ p3) ∨ (True ∨ True))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589453096388502361579381218009 : ((((((True ∧ ((p3 ∧ p5) ∧ (((p1 ∨ p5) ∧ (((((p4 ∨ p3) ∨ p1) ∨ p4) → (False ∨ p3)) ∨ p5)) → False))) ∨ p5) → False) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769689167448154380959205299689 : (((p5 ∧ (p1 ∨ ((((((((p3 ∧ p3) ∨ ((p2 ∧ True) ∧ p5)) → True) → p5) ∨ (p1 ∧ p5)) ∧ (p5 → (p3 ∨ p5))) ∨ False) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54717113041527478129808655050 : (((((p1 ∨ p5) → (p4 ∧ p2)) → (p5 → p1)) → (((p4 ∨ (p3 ∨ ((True ∨ ((False ∨ p5) → p1)) → p2))) → p3) ∨ (p2 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336406986189230130708940917737 : (p1 → ((p5 ∧ ((((((True → (((p3 → p5) ∨ (p1 → p4)) → (p1 ∧ p5))) → p5) → p5) ∨ p1) → (False ∨ (p2 ∨ p5))) ∨ p3)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60442804018560509458552377608 : (((p5 → True) → ((p2 ∨ (p1 ∨ ((((p3 ∨ p3) ∧ p2) ∧ (p1 → p2)) ∨ (((p5 ∧ p4) ∨ p2) ∨ p5)))) ∨ (False → (p3 → p3)))) ∨ p2) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135069276039147970822072582134 : (((((p4 → False) ∨ (p4 ∧ (p1 ∨ (((True ∧ True) → p1) ∧ ((False ∧ p5) ∧ p5))))) ∧ (p4 → p1)) ∨ (p5 → True)) ∨ (p1 → (p3 ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635763525132892377505202808064 : ((((((p2 ∨ (((((False → p5) → (p1 ∨ False)) ∨ p3) → (p3 ∨ (False ∧ False))) ∨ p5)) → p5) → (((p1 ∨ p3) ∨ p1) → p2)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200668089049617478548752021537 : ((p1 ∧ ((p4 → True) → (p1 ∨ (p4 ∧ p1)))) → ((p5 → (p4 ∨ (p1 ∧ p2))) ∨ ((p1 ∧ (((p3 ∧ p2) → p5) → False)) → (p1 ∨ False)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356374175047068696689645012552 : (p5 → ((((((p2 ∨ True) → (p4 ∨ p1)) ∨ (p1 ∧ p2)) ∧ (p5 ∧ p4)) ∨ p1) → ((p1 ∨ p3) → (((p2 → False) ∧ (p3 → False)) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h7.left
        let h15 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h20.left
        let h23 := h20.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Conjunctions on the left can always be decomposed.
        let h27 := h20.left
        let h28 := h20.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h29 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53908664838744413509937930086 : (((p5 ∧ (p1 ∨ ((p5 → (p1 → (p4 ∧ p4))) → p1))) ∨ ((p2 → (p5 → p3)) → (False → ((p1 ∧ p2) ∨ ((p3 → True) → False))))) ∨ p1) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114950852546483195628297572118 : (((True ∧ ((p2 ∨ (p2 ∨ ((p2 → p4) ∨ True))) → ((p3 ∧ p1) ∧ p5))) → (p1 ∧ ((((True ∧ True) ∧ False) ∨ p3) ∧ p3))) ∨ (True → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p2 ∨ (p2 ∨ ((p2 → p4) ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : (p2 ∨ (p2 ∨ ((p2 → p4) ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- One of the premise coincides with the conclusion.
  exact h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
  have h16 : (p2 ∨ (p2 ∨ ((p2 → p4) ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h15, we can now drive its conclusion.
  let h17 := h15 h16
  -- We need to get the left conjuct of h17 based on <expert-advice>.
  let h18 := h17.left
  -- We need to get the left conjuct of h18 based on <expert-advice>.
  let h19 := h18.left
  -- One of the premise coincides with the conclusion.
  exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149860361037946175591829409629 : ((p2 ∨ ((((p3 ∨ True) ∨ (p4 → (p1 → (True ∨ (p3 ∨ (p1 → p4)))))) ∧ ((p3 ∨ False) ∧ p3)) ∧ False)) ∨ (((p1 → p2) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605975856724955540439112869421 : ((((p5 → ((p4 ∧ (((p3 ∨ (p2 ∨ p2)) ∨ (p5 ∨ p3)) ∨ True)) ∧ ((p3 → p5) → (p5 ∧ ((True ∧ (p4 → p5)) ∧ p2))))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147517265594707808912739425652 : (((p4 ∨ (((p1 ∨ p2) → (p2 ∨ (p2 → False))) → (p2 ∧ (p4 ∧ ((p1 → p5) → (True → p3)))))) ∨ p4) ∨ ((False ∧ (p1 ∧ p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199760069222490101555350896027 : (((False → ((p1 ∨ False) ∨ (p1 → p3))) → p4) → (p4 → ((((p3 ∧ (((p4 → p1) ∨ (p2 → p4)) ∨ (False ∨ p2))) → p5) ∨ True) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



