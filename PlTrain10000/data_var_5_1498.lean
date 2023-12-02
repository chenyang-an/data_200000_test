variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256597344328575204465533169316 : ((p1 ∨ True) → (((False ∨ p2) ∧ (p1 ∨ (p1 ∧ ((p5 → ((p4 ∧ False) ∧ p5)) ∨ (p2 → p2))))) ∨ (p2 → (True ∨ (p2 ∧ (p1 ∧ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809262894599110563911935515362 : (((p5 → ((((p1 ∧ (p5 ∨ p3)) → (p1 ∧ p4)) ∧ ((True → (p2 ∨ ((False → p2) → ((p5 → p3) → p2)))) ∨ (True → True))) ∨ p5)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_354644414130001770662033463723 : (p5 → (((((True → ((p1 ∨ ((p5 ∨ p4) → (True ∧ p1))) ∨ (True ∨ (((True ∨ (False ∨ False)) ∨ False) → p1)))) ∨ p5) → p5) → p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160420305541067554746564407277 : ((((p3 ∧ (True ∨ p1)) ∧ (p2 → (True → ((p5 ∧ (p3 ∨ p1)) ∨ p5)))) ∨ ((True ∧ False) ∧ p1)) → (((False → False) → p4) ∨ (p2 → p5))) := by
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
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h9 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h10 := h4 h9
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h12 := h10 h11
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h17 =>
          -- One of the premise coincides with the conclusion.
          exact h14
      case inr h18 =>
        -- One of the premise coincides with the conclusion.
        exact h18
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h21 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h20
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h22 := h4 h21
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h23 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h24 := h22 h23
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- One of the premise coincides with the conclusion.
          exact h26
        case inr h29 =>
          -- One of the premise coincides with the conclusion.
          exact h26
      case inr h30 =>
        -- One of the premise coincides with the conclusion.
        exact h30
  case inr h31 =>
    -- Conjunctions on the left can always be decomposed.
    let h32 := h31.left
    let h33 := h31.right
    -- Conjunctions on the left can always be decomposed.
    let h34 := h32.left
    let h35 := h32.right
    -- False on the left can always be used.
    apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587652092270463726894808441084 : (((((((((True ∧ ((((False ∨ p5) → (p1 ∧ p4)) → True) ∨ p3)) ∨ p4) → p1) → ((p3 ∨ p2) ∨ (True ∧ False))) → False) ∨ p1) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77827572207095616031099047070 : (((False ∨ ((((p3 ∧ ((((p1 → p5) ∨ p2) → p2) ∧ True)) ∨ ((p4 ∨ (False ∨ (False ∧ p3))) ∨ True)) ∧ (p3 ∨ True)) ∨ True)) → False) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ ((((p3 ∧ ((((p1 → p5) ∨ p2) → p2) ∧ True)) ∨ ((p4 ∨ (False ∨ (False ∧ p3))) ∨ True)) ∧ (p3 ∨ True)) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166326575429624001518436124048 : ((p5 ∧ ((True ∨ (p3 ∧ (True ∨ p1))) → (((p2 ∧ (p4 ∨ (p4 ∨ False))) → p1) ∧ False))) ∨ (((p3 ∨ True) ∧ (p4 → p4)) ∨ (p2 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323487489127203318601222247865 : (p5 ∨ (((((((p5 ∨ False) ∧ True) ∨ (((p1 → p4) ∧ p5) ∧ p2)) ∨ ((True ∧ p1) → p4)) ∧ p2) ∨ (False → p4)) ∨ ((p4 → p4) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773399176332552951773849913572 : (((False ∨ ((p4 → (((((p3 → p5) ∧ (p5 ∨ ((p1 → p2) → p3))) ∧ (False → p5)) ∧ False) ∨ (p5 → ((False → p3) ∧ p4)))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129708791578875982366926483553 : ((((((False → True) ∨ (p3 ∧ (True → p2))) → p4) ∧ ((p2 → (p5 ∨ p5)) ∨ ((p3 ∨ (p1 ∨ p1)) → p3))) → p4) ∧ (False → (p3 ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((False → True) ∨ (p3 ∧ (True → p2))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : ((False → True) ∨ (p3 ∧ (True → p2))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h9
    -- One of the premise coincides with the conclusion.
    exact h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619528875142879627225918031456 : (((((p4 → (p4 ∨ False)) → ((p3 ∧ p4) ∧ ((((p1 → ((False → p4) ∨ p1)) ∧ ((True ∧ p1) → (p1 → p3))) ∧ p4) ∧ False))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_86613191102912726673900139354 : (((((p1 ∨ (p2 ∨ True)) → False) ∨ (p2 ∧ False)) ∧ ((p3 ∨ False) → (((p3 → ((p3 ∨ p5) → (True ∧ p3))) ∨ (p2 ∧ p4)) ∧ p5))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p1 ∨ (p2 ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183802419250200579127442347687 : (((((False ∧ p5) ∧ ((p1 ∨ (p5 ∧ p5)) → p2)) ∨ p2) ∧ p1) ∨ (p5 → (((p4 ∧ ((p5 ∧ (False ∨ True)) ∨ False)) ∨ p3) ∨ (p3 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137045801539267090632600481297 : (((False → p1) → ((p4 ∧ (p3 → p1)) ∧ (False ∧ (((p2 → (p5 ∨ (p4 → True))) ∨ p4) ∨ ((p2 → p5) ∨ p4))))) ∨ (p5 ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177691259533405288995428981226 : (((((True ∧ p1) ∧ ((p3 ∧ (p1 ∨ False)) ∨ p5)) ∧ (p5 ∨ False)) ∧ p4) ∨ (p5 → (((p4 ∨ (p2 ∨ p5)) ∨ (p3 → (p2 ∨ p3))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309737747278059706409960668811 : (p2 ∨ (((False ∧ (((p1 → p3) → ((((p3 → p5) → p3) ∨ ((p1 ∧ p5) → True)) ∧ p2)) ∨ p3)) ∨ True) ∧ ((p2 ∨ (p5 → p5)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37154700698025425973370439982 : ((((((True ∧ (((((p3 → p3) ∨ p5) ∧ (True → p1)) → (p3 ∨ False)) → p2)) → (p3 → p1)) → (p4 → (False ∧ p1))) ∧ p4) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44597024147027818412453076703 : (((((p1 ∧ (((False ∧ p4) ∨ p3) ∨ True)) ∨ False) → (p4 → ((p3 ∨ (True → (p5 → (p4 ∨ True)))) ∨ ((True ∧ False) ∧ p1)))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60222544019314942144255236756 : (((True → p2) → ((((((p1 ∧ False) ∨ (p1 ∨ (p3 → p4))) → False) ∧ ((((True → p2) ∨ p4) ∧ p3) → False)) ∨ (True ∧ p2)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60929034211472985979694543270 : ((False ∧ (((p5 ∨ (p1 → p5)) ∧ ((p2 ∨ p2) ∨ ((p2 ∧ p1) ∨ (((p2 → (p2 ∨ (False ∧ (p3 → p1)))) ∧ p4) ∧ p2)))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774821069197883062694816103634 : (((False ∨ ((p1 → (False ∨ ((True ∨ p3) → p1))) → (((p2 ∧ ((p3 → p1) ∧ p3)) ∨ ((p1 ∨ (p2 → p5)) → (False → p4))) ∨ p3))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115893871315670576898435197382 : ((((p3 → (True → p4)) ∨ p3) ∨ ((((False → p4) ∧ ((p2 ∨ (p4 → p5)) → (p5 ∧ p1))) → ((p1 ∧ p1) ∧ p5)) ∨ p3)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699974126325835808537831096860 : (((((((p1 ∧ p2) → p3) ∨ p4) ∨ (p1 ∨ ((False ∧ p4) → p2))) → (((True ∧ (((p1 ∨ p1) ∧ p4) → (p4 → p2))) ∧ p2) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52470162104005542409246281846 : (((p3 ∨ (((p5 ∧ True) ∧ ((False → ((p4 ∧ p3) ∧ p2)) → p3)) → p3)) ∧ (p3 ∨ ((True ∨ (p1 → p4)) → (p1 ∨ (p5 ∨ True))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : (False → ((p4 ∧ p3) ∧ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h7
    -- False on the left can always be used.
    apply False.elim h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h6
  -- One of the premise coincides with the conclusion.
  exact h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h9
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320184578045240693893048150777 : (p4 ∨ ((True ∨ p3) ∧ ((p1 ∧ ((p5 ∨ (p5 ∧ ((True → (p5 → p5)) ∧ p5))) ∨ (p2 ∧ (p3 ∧ p5)))) ∨ (True → ((p1 → p1) → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115417254378080249299591898705 : (((((((True ∧ p1) → True) ∨ False) → p1) ∧ True) ∨ ((p4 ∧ (p3 ∨ (((True ∧ p3) ∨ (p5 → p2)) → (p3 ∨ p2)))) → p3)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179421656018355399639263644776 : ((p4 ∨ (((((p4 → True) → p5) ∨ p4) ∨ p4) ∨ (p4 ∨ (p5 → True)))) ∨ (False ∧ (p5 ∧ (p5 → (True → (p3 → ((p3 ∧ False) ∧ p5))))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193688399712677373720754071683 : ((p1 ∧ (((True ∨ p4) ∨ True) ∧ (p5 → (p2 ∨ p5)))) → ((p4 → p4) ∧ ((p4 ∧ (False ∧ (((p5 ∨ p4) → False) → p4))) ∨ (False ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h12.left
  let h14 := h12.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h18 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258172428989362255278086268359 : ((p4 ∨ p4) → ((True ∧ (((((((p3 ∧ p5) → p1) ∨ p1) ∨ False) ∧ (p1 ∨ p2)) ∨ (p5 ∧ p3)) ∧ (False ∨ p3))) ∨ ((p2 ∨ p4) ∨ False))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306061656786473245842221519426 : (p1 ∨ ((p5 ∧ (p4 → (p5 → False))) → (p2 ∨ (((((p2 ∨ True) → (False → p4)) → True) ∧ ((False ∧ False) ∨ (p2 ∧ (False ∧ p2)))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257593526941982660253466132481 : ((p3 ∨ p1) → (p1 ∨ (((p2 → ((False → p3) ∧ p5)) ∨ (p2 → False)) → ((((True → ((p5 → p1) → (p4 ∨ True))) → p3) → p4) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_36328992266199550262390054366 : ((p4 → (((((p1 ∧ ((p5 ∨ p1) ∨ (p2 → ((p2 → p2) ∨ (p1 → p1))))) ∨ p4) ∧ p2) ∨ (p4 → (p4 ∧ p1))) ∨ (True → p4))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234607333960256768980898831766 : ((p3 → (p4 ∨ p4)) → (((p5 ∧ (p1 ∨ True)) ∧ ((((p2 ∨ ((p5 ∨ (p3 ∨ (p2 ∧ p2))) ∧ p4)) → p1) → p5) ∧ p1)) ∨ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44647710180074651231729464723 : ((((((p3 ∨ p1) ∧ (p2 → p3)) → p3) ∨ ((p1 ∧ ((p4 → (p4 ∧ ((p5 → ((True ∧ p1) ∧ p5)) ∧ True))) ∧ p1)) ∧ p5)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322359002493499878783561009343 : (p5 ∨ (((p1 ∨ (True ∧ ((p3 ∨ ((((True ∧ p1) ∨ p4) ∨ p3) → (p4 ∨ (p1 → p4)))) ∨ (p4 ∨ p3)))) ∨ (True ∨ (False ∨ p5))) ∨ p3)) := by
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
theorem thm_5_vars_227597996139025626534524241344 : ((False ∧ (p4 ∧ False)) ∨ ((p3 ∧ False) ∨ ((False ∧ False) → (((((p5 → p5) ∨ (p1 → p4)) ∧ True) ∧ ((p4 ∧ p2) ∧ (True ∧ p2))) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157802050023177672578371099042 : (((p1 → (p4 ∨ (p5 ∧ (p4 → (p1 ∨ (True → (p5 ∧ True))))))) ∨ (((p2 ∨ p2) ∨ p3) ∧ p5)) ∨ (p2 → (p4 → (False → (p4 → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81058139872280884555033326195 : ((((((p3 ∧ (p3 → p2)) ∧ p1) ∧ p1) ∧ (((p2 → True) → p1) ∧ ((p1 ∧ (p4 → (p1 ∨ p2))) → p5))) ∧ (p2 ∨ (p5 ∨ False))) → p2) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h5.left
  let h13 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h14 =>
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h17 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h18 := h11 h17
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208112884193245365387001720158 : ((((p5 → p3) ∧ True) → (p3 ∨ True)) → ((p4 ∨ (p2 ∨ (((p4 ∨ ((p5 ∧ True) ∧ p4)) → False) ∧ p2))) ∨ ((False → (p1 ∨ p2)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166422314801006826975875758367 : ((p1 ∨ ((((p1 → False) → (p1 → p4)) ∨ p3) → (((p3 → (p1 ∧ p5)) ∧ True) → p1))) ∨ (p2 → (p2 ∨ ((p1 ∧ True) ∨ (p4 ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135367054935953515506674004407 : ((((((False → p4) → ((((p1 ∧ p1) → p3) ∨ p5) ∨ (p5 → (True ∧ p3)))) ∨ p2) ∧ False) ∨ (False ∧ (True ∨ p1))) ∨ ((False ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257185458943677243862243270186 : ((p2 ∨ p2) → ((((True ∨ ((p5 → (False → p4)) → (True ∨ ((((p4 ∧ False) ∧ p1) ∧ p4) ∧ p5)))) ∨ p5) → (p3 ∨ (True → True))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h6
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115945248618572920009727159658 : (((p2 ∨ (p5 → (p5 ∧ p3))) ∨ (((((False ∧ False) ∧ (p1 ∧ p2)) → (p5 → p2)) ∨ (p1 ∨ True)) → ((p5 ∨ p4) ∧ p1))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738346488438359898057597142107 : ((((p1 ∧ False) ∨ ((((True ∨ (p2 ∨ (((p3 → p1) ∨ p3) ∨ p4))) ∨ ((p2 ∨ False) ∧ (p4 ∧ p2))) ∧ ((p5 ∧ p5) ∧ p4)) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_777885509006012403148927728163 : (((p1 ∨ ((p1 ∨ (p2 → (False ∨ p3))) → (((((p3 → p4) ∨ (p4 ∧ p3)) ∨ ((True ∧ (p5 ∨ True)) ∨ p4)) ∨ False) ∧ (p1 ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44457739759685366233635542047 : (((((p2 → p4) → (p2 ∨ (p4 ∧ (False → ((p4 ∧ p3) ∧ True))))) ∨ (p3 ∧ ((p2 → ((p2 → p3) ∧ (p1 ∨ False))) → p4))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247919452594568571904158082963 : ((p1 ∨ p3) ∨ ((p5 ∨ (((p2 ∨ False) ∨ p1) → True)) ∧ (p3 ∨ ((p5 ∧ (((p3 ∨ ((p2 → False) ∨ (True → False))) ∨ p2) ∨ True)) ∨ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303991647339456457429230124757 : (p1 ∨ (((p3 ∧ p4) ∨ (((True ∨ (((p3 → (p3 → p5)) ∨ ((p4 ∧ p3) ∨ p4)) → p1)) → False) ∨ (True ∨ ((p1 ∨ False) ∧ True)))) ∨ p2)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184419922045837179271929449627 : ((((p3 → (p1 ∧ ((p4 ∨ p5) ∧ p2))) → p4) ∧ (p3 ∨ False)) ∨ ((p5 ∧ (p5 ∨ p5)) ∨ (((((p1 → True) ∧ True) ∧ False) ∧ True) → p4))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66821721510354685036511914341 : ((True → (True → (p4 ∧ (True ∧ ((((p1 ∧ ((p3 → p2) ∨ ((p5 ∨ (True ∨ p4)) → p5))) → p1) → p4) ∧ (p3 ∧ (p1 ∨ p1))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806408232124292874389477354939 : (((p4 → ((p4 → (((((p2 ∧ (p2 ∨ True)) ∨ p1) → (False ∨ p3)) ∧ p5) ∨ ((True ∧ (p3 → ((p1 → p2) ∧ p1))) ∨ p1))) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_265604391059171675113797913730 : (True ∧ (p1 ∨ (((p2 ∨ p4) ∨ p1) → ((((p5 ∨ p5) ∨ (True ∨ (True ∧ p1))) ∨ ((p3 ∧ ((p5 ∧ p2) ∨ False)) ∧ p5)) ∨ (p4 ∨ p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181270524242239205936823125001 : ((p4 ∧ ((p1 ∧ p5) ∨ (True ∧ (p2 ∨ (p1 ∨ (False ∨ (p3 ∨ p4))))))) → ((((True ∨ True) ∨ ((p2 ∧ p4) ∨ p3)) → p5) ∨ (p4 ∨ p4))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- False on the left can always be used.
          apply False.elim h14
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148958760459835900905608647955 : ((((p1 ∧ False) ∨ True) ∧ (((p3 → (False → p1)) ∨ p4) ∧ ((True → p1) ∨ ((p2 → (True → False)) → p5)))) ∨ ((True → False) → (p5 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171956653177946590521642961760 : ((((True ∨ (p5 → p5)) ∧ ((p2 ∧ (False ∧ (p2 ∨ p2))) ∨ p3)) ∧ (True ∧ p4)) ∨ ((False → p4) ∧ (((False → True) ∨ (p5 ∨ True)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51479307330722225689448152593 : ((((False ∨ (p3 ∧ ((p3 ∧ True) → p4))) ∧ ((True → False) ∨ ((p5 ∨ p5) ∧ (p5 ∧ p3)))) → ((p4 → (True → p4)) ∧ (p1 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149048402992563419014003810495 : (((True → (p5 ∧ p3)) ∨ ((((((True → (p2 → False)) ∧ (p3 → p3)) → p4) → p2) → (p3 ∧ p2)) ∨ True)) ∨ (p2 ∧ (True ∨ (False ∧ p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342287906804670114756084243424 : (p2 → (((True ∧ ((p1 → p2) ∨ (p3 → p5))) ∧ (p1 → (((p2 ∨ p1) ∧ True) → (False ∧ False)))) ∨ (((p3 → (p4 ∨ p5)) ∨ p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764774826506226314905341801047 : (((p4 ∧ (((p1 ∨ ((((True ∨ True) ∧ p4) → (((p3 → p2) → ((((p2 ∨ p2) ∧ p4) ∧ True) ∧ p1)) → p5)) ∧ p4)) ∧ p4) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670998677393091474254337978951 : ((((p5 ∧ (p3 ∨ (((p2 ∧ ((p2 ∨ p3) ∨ p5)) ∧ ((p2 ∧ p1) → ((p4 ∧ False) → p2))) → (p1 ∨ p3)))) ∨ (p3 ∨ (p3 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786637663835675991762672423748 : (((p4 ∨ (((p1 ∧ (True ∨ (False ∧ True))) → (p5 → p3)) → ((False ∧ (False ∨ (p4 ∧ p5))) ∨ ((p2 ∨ False) ∨ (False ∨ (False → p3)))))) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264311598356394526315035363485 : (True ∧ (((p1 ∧ True) → (p3 ∧ (p4 ∨ p4))) → ((True ∨ p1) → ((((p5 ∨ (p3 ∧ (p2 ∨ p1))) ∨ (True ∨ p4)) ∧ (p5 ∨ True)) ∨ p2)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117383231626870865805763700644 : ((p1 ∧ (((((p1 ∨ ((p4 → p3) → ((p3 ∨ p1) ∧ (p2 ∨ (False → False))))) ∧ (p5 ∧ p5)) ∨ p5) → (p4 → p1)) ∧ True)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174854258137216371550688972214 : (((p3 ∨ False) ∨ (((p3 ∨ ((p1 ∧ ((True → False) → p3)) → p5)) ∧ p4) → p4)) → (((p2 ∨ p3) ∨ p3) ∨ (p3 ∨ ((True → p2) → p2)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h6
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723133668185353081888472056956 : (((((p5 ∨ p3) ∨ False) ∧ ((((p4 → p4) ∧ ((p5 ∨ (p3 ∧ ((p2 → (p3 ∧ p1)) ∨ ((False ∨ p4) ∨ p1)))) → p3)) ∧ p4) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634366201785973520203044754910 : ((((((((False → (p1 ∧ True)) → (p2 ∨ (p5 → p4))) → (False → (False ∨ (p3 → (True ∧ p3))))) ∧ p3) ∧ (False ∨ (p5 ∧ p1))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781609048920973258392095598679 : (((p2 ∨ (p1 ∨ (((p3 ∨ p1) ∧ p5) → (p3 ∨ (((p5 → p5) ∨ ((False ∨ (p2 ∧ p4)) → p3)) → ((p2 ∨ p4) ∨ (False → p5))))))) ∨ p2) ∧ True) := by
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
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307623494919462977539563319775 : (p1 ∨ (p1 → ((((p2 ∨ (True → (((((True → p2) ∨ p1) → p2) ∧ False) ∧ p1))) ∨ (True ∧ p4)) → False) ∨ (((p4 ∧ p3) → p3) ∨ True)))) := by
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
theorem thm_5_vars_219987635894113726791248603593 : ((p5 → (p5 ∧ (p1 ∧ p2))) → (((p2 ∨ p5) → (p3 → (True ∧ p4))) ∨ (((p3 ∨ (p1 ∨ (False → (p4 ∧ p5)))) ∧ True) → (p1 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50707282637285002217349501659 : ((((p3 ∨ p3) ∧ (((p4 → (True → ((True ∨ (p3 ∨ (p4 ∧ True))) → p1))) ∨ (p5 ∨ True)) ∧ p1)) → (p5 ∨ ((False → False) → p1))) ∨ p3) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h9 =>
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
        -- Implications on the right can always be decomposed.
        intro h12
        -- One of the premise coincides with the conclusion.
        exact h6
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h21
        -- One of the premise coincides with the conclusion.
        exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47486639909399869104893280226 : (((False ∨ ((((p4 → (p2 ∨ (((p5 → False) ∨ False) → False))) → (p4 → p3)) → ((False ∨ False) ∧ p3)) ∨ (True ∨ True))) ∨ (p2 ∧ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_307415473635086937078731408300 : (p1 ∨ (p4 ∨ (p5 → (((p4 ∨ ((p5 → (True → (p4 → True))) → ((((p2 ∨ False) → p2) → p4) ∧ ((True ∨ p4) ∧ p3)))) ∨ p5) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55103455414848434198710150276 : (((p5 → (((p2 ∧ False) → p4) ∨ p3)) ∧ (((p2 ∨ p5) → (False ∨ p3)) ∨ (((p4 → (False → (p5 → (False → p5)))) → p2) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37504483806351345169008008729 : (((((p3 → p3) ∧ ((((((p2 → True) ∨ True) → (p5 ∧ False)) ∨ p2) ∨ (p3 ∧ False)) ∨ ((True ∧ (True ∧ p4)) ∧ p3))) ∨ p3) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68322225484248719088732268796 : ((p3 → ((p3 → (p3 → ((p3 ∧ ((True ∧ False) ∨ ((True ∧ p2) ∨ (False ∧ False)))) ∧ True))) ∨ (((p1 ∧ p5) → False) ∨ (p5 ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711544970371154421991992448589 : ((((False → ((p5 → p5) → (False ∨ p2))) ∧ (p2 ∨ (p1 ∨ ((p2 ∨ p1) ∨ (((p2 ∨ p4) ∨ (True ∧ p1)) ∨ (p2 ∧ (True → p4))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158197083663632193513896606972 : ((((p3 ∨ p5) ∧ False) ∧ (False ∧ (((False → (False → p5)) ∧ (p4 → p1)) ∧ ((True ∧ p4) → False)))) ∨ (True ∧ (p4 → ((True ∨ p3) ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_548155140512124700604491303064 : (((False ∨ (((False ∧ ((True ∨ p5) ∨ (False → p1))) ∨ True) ∧ (((p1 ∨ (((p5 ∧ p4) ∧ p2) ∨ True)) ∧ p2) ∨ (True ∨ (p4 → True))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341978967958053168829492788935 : (p2 → ((((p3 ∨ False) ∧ (True ∧ ((p4 ∧ ((((p3 ∧ p1) ∨ p3) ∨ p3) ∧ p1)) ∨ (p2 → p4)))) ∧ (p2 ∨ False)) ∨ (p3 ∨ (p1 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166239526097127479762562093456 : ((p2 ∧ (p4 ∨ ((p3 ∧ (p1 → ((p3 ∨ (p2 ∧ (False → (p5 ∨ False)))) → True))) → p5))) ∨ ((((p3 ∨ p4) → p4) ∨ True) ∨ (p1 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198361369617232361282415364606 : ((p2 ∧ (p1 → ((False ∧ p4) ∨ (p2 ∧ p4)))) ∨ (p3 ∨ (((((p2 ∧ p5) ∧ False) ∧ (True ∨ ((False ∨ p4) ∨ p2))) ∧ (p3 ∧ True)) → p4))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66246182225974459872134628125 : ((p5 ∨ ((((p4 ∨ p5) ∧ p3) ∨ (p1 ∧ p4)) → ((((True ∧ p4) ∨ p3) ∧ ((p2 ∧ (False → p4)) ∨ (True → (p4 → True)))) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_923268414297589579990636666094 : ((((((p1 → (((p1 ∨ p2) → (True ∨ p1)) → p4)) → p5) → p1) ∧ (p5 ∧ (((p3 ∧ False) ∨ p3) ∨ ((p2 ∨ p5) ∧ (p5 → True))))) → p1) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
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
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : ((p1 → (((p1 ∨ p2) → (True ∨ p1)) → p4)) → p5) := by
        -- Implications on the right can always be decomposed.
        intro h12
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h13 := h2 h11
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h17 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h18 : ((p1 → (((p1 ∨ p2) → (True ∨ p1)) → p4)) → p5) := by
        -- Implications on the right can always be decomposed.
        intro h19
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h20 := h2 h18
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h21 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h22 : ((p1 → (((p1 ∨ p2) → (True ∨ p1)) → p4)) → p5) := by
        -- Implications on the right can always be decomposed.
        intro h23
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h24 := h2 h22
      -- One of the premise coincides with the conclusion.
      exact h24
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55793126263866441952691849401 : ((((p1 ∨ p4) ∨ (p5 ∧ p4)) ∧ (((((p3 → (p2 ∨ True)) → False) → (False → (False → True))) ∧ p3) → ((p1 ∨ p2) → (p2 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255176689847274977766712003003 : ((p4 ∧ p4) → ((((True → (False ∨ True)) ∨ (p1 ∨ p5)) → (((False ∧ p3) ∨ True) ∨ (p2 ∧ (p5 ∧ (((p5 → p3) ∨ True) ∧ True))))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h1.left
      let h9 := h1.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h1.left
      let h12 := h1.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214953330530388514546289190638 : (((p2 ∧ True) → (p5 ∨ p5)) ∨ (p2 ∨ ((p5 ∧ (p3 ∧ True)) ∨ ((p5 → ((p3 ∨ p5) ∧ p5)) ∨ ((p5 → True) ∨ ((False → p3) ∧ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48958812133038977653633661755 : ((((p4 → (p3 ∨ ((False ∨ False) ∧ ((((((p1 → p5) ∧ p1) → p5) → (p4 ∧ p2)) ∨ p5) ∧ p2)))) ∧ False) ∨ ((True ∨ p1) ∨ p3)) ∨ p4) := by
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
theorem thm_5_vars_114114212137781336992096515647 : (((p3 ∨ (((False ∧ ((p2 → (p4 → ((p2 → (False ∧ p1)) ∨ (False ∨ False)))) → p5)) → p5) → p5)) ∨ ((p3 ∨ p5) → True)) ∨ (p3 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150034175573607368435132175684 : ((p5 ∨ (p2 ∧ (((False → (((False ∨ p3) ∧ p5) → (p4 ∨ True))) ∧ ((True → False) ∨ (p1 ∨ p1))) ∨ p2))) ∨ ((p3 ∧ (p1 → p2)) → p3)) := by
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
theorem thm_5_vars_38874424819614415363839892448 : ((((p4 → (False ∧ p3)) ∧ (p3 ∧ (p5 ∧ ((((p2 ∧ (p3 ∧ p2)) ∨ p4) → True) ∧ ((p5 → p3) ∧ ((False → True) → p1)))))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136277774849406465543377178265 : (((((p3 → p1) ∧ p2) → (p5 ∨ p5)) → ((p5 ∧ (p4 ∨ ((p1 → False) ∧ ((p3 ∨ p3) ∨ p3)))) ∧ (p3 ∧ False))) ∨ (p3 → (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47688894213510949639240210413 : ((((p5 ∧ (p5 ∨ (p4 ∧ (((((p3 → True) ∧ (p5 ∨ True)) → ((False → (False ∨ p2)) ∨ False)) → p1) ∨ p5)))) ∧ p5) → (p3 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323899248517158330806139882238 : (p5 ∨ (((((p1 ∨ p5) ∨ (True → False)) ∨ (p2 → p5)) → (p2 → ((p3 ∨ p3) ∨ p4))) ∨ (p1 ∨ ((False ∨ p3) → (p4 → (True ∧ True)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49017405298634675987440434849 : ((((((p1 ∨ ((p3 → p5) → p1)) ∨ (((False ∨ (True ∧ p3)) ∨ (p5 ∧ True)) → False)) ∨ (True ∧ p3)) → False) ∨ (False → (p1 → p5))) ∨ False) := by
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
theorem thm_5_vars_225444968373125268589053989165 : (((p4 ∨ True) ∧ p1) ∨ ((p2 ∧ (p4 ∨ (((p3 → (False → (p1 ∨ p5))) ∨ (p3 ∨ p3)) ∧ p5))) ∨ (True ∨ ((False ∧ p1) → (p5 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187379405849781791883119334506 : ((p3 ∧ (p4 ∨ ((((p2 ∧ p5) → False) → p1) ∨ (p4 ∨ p3)))) → (((p5 ∨ p5) ∨ ((True → (p4 ∨ p3)) ∨ True)) ∨ (p2 ∨ (p3 ∨ p4)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123334901832541434325053443687 : (((((p5 ∨ p1) ∧ (True ∧ p3)) ∨ (((((p4 ∧ (p4 → True)) → p5) ∧ p3) → p1) ∧ True)) ∨ (False ∨ ((True ∨ p2) ∨ True))) → (p2 ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h5.left
        let h8 := h5.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h5.left
        let h11 := h5.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h20 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h20
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314318451141823871476247589148 : (p3 ∨ (((((p2 → True) → (p1 ∨ ((p1 ∨ p3) → True))) → p2) ∧ ((True ∧ True) ∨ (True ∨ (p1 ∨ (False → p5))))) → (True ∧ (p1 ∨ p2)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : ((p2 → True) → (p1 ∨ ((p1 ∨ p3) → True))) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h13 : ((p2 → True) → (p1 ∨ ((p1 ∨ p3) → True))) := by
        -- Implications on the right can always be decomposed.
        intro h14
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h16 := h2 h13
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h19 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h20 : ((p2 → True) → (p1 ∨ ((p1 ∨ p3) → True))) := by
          -- Implications on the right can always be decomposed.
          intro h21
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h22
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h23 := h2 h20
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605142108338654066301613828644 : ((((p2 → (((p2 ∨ ((True ∧ p5) → p2)) → ((p3 ∧ p5) ∧ (p5 ∧ p5))) ∧ (p2 → ((p5 ∨ (True ∨ p4)) ∧ (p2 ∨ p3))))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300698943348842281326451280080 : (False ∨ ((((((False ∧ p2) ∨ (p3 → (((p1 ∧ p2) ∧ (p4 ∨ False)) ∧ p2))) ∨ p3) ∧ p4) ∧ p1) → (((False ∨ True) ∧ (p1 ∧ False)) ∨ True))) := by
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
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
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



