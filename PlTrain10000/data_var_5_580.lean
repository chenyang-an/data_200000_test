variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241358223439448993528339455461 : ((False → False) ∧ (((p1 → (True ∨ True)) → (p3 → ((p2 → p1) ∧ False))) ∨ (((((p2 ∧ p4) ∨ (p3 ∨ True)) ∨ p4) → (p1 → p1)) ∨ p1))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135373197848533350083362647839 : ((((((p5 ∧ (p1 ∧ (True → ((p4 ∧ p5) → ((True ∧ False) ∧ p5))))) ∨ p3) ∧ p3) ∨ p3) ∨ ((p4 → p4) ∨ p4)) ∨ ((True ∧ True) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337561192581524355593984378105 : (p1 → ((p5 → (((False ∨ p4) ∧ (((p1 → p3) ∨ p1) → ((((p5 → p1) ∧ p2) → p4) ∧ p5))) ∧ False)) ∨ ((True ∨ (p2 → True)) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199863119143001924506920611569 : (((p4 ∨ (p4 ∧ (p2 → False))) ∧ (p2 ∨ p5)) → ((p1 ∧ (p1 ∧ p3)) ∨ ((p4 → ((True → False) ∧ p3)) → (True → (False ∨ (p1 → p1)))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h16 =>
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h17 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h18 := h15 h17
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- Implications on the right can always be decomposed.
      intro h21
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- One of the premise coincides with the conclusion.
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221713168411505043352814579635 : (((False ∧ False) → p3) ∧ (p4 ∨ (((True ∧ ((p3 ∧ ((p2 → (p3 ∨ (p2 ∧ p5))) ∨ (p3 ∧ p4))) → ((True → p1) → p4))) → p2) ∨ True))) := by
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
theorem thm_5_vars_614923756756328091682259732642 : (((((((False ∨ ((True ∧ False) ∨ (((p3 ∧ True) ∧ p3) ∧ False))) ∧ (True ∧ (p3 ∧ p1))) → p2) → (p2 ∧ ((p2 ∨ False) ∨ p4))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148871676036875004619924963238 : (((((False → p1) → True) ∧ p4) ∨ (((p2 ∧ False) ∧ p1) ∨ ((((p4 ∨ p5) ∨ False) ∨ (p2 → False)) ∧ True))) ∨ ((p5 ∨ p2) → (p5 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147085549664496576984896214895 : (((((p3 ∨ p2) ∨ (p2 ∧ p5)) ∨ ((True ∨ ((p2 ∨ (p1 ∨ True)) ∧ (p4 ∧ (True ∧ p3)))) ∧ True)) ∧ p3) ∨ ((p2 → (p4 → True)) ∨ p4)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327365599977539502082468235966 : (True → ((((p5 ∨ ((((p4 ∧ p5) → p1) ∨ (p5 ∨ p4)) ∧ (((False ∨ (False ∧ p5)) ∨ (p5 → p1)) ∨ p2))) → p4) ∧ (True ∧ p1)) → p4)) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : (p5 ∨ ((((p4 ∧ p5) → p1) ∨ (p5 ∨ p4)) ∧ (((False ∨ (False ∧ p5)) ∨ (p5 → p1)) ∨ p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h12 := h3 h7
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675108998392801248049081451381 : (((((((p3 → p3) → (p4 → (((p1 ∨ p3) → (p4 ∧ (p3 ∧ (p4 ∨ p5)))) → p5))) ∨ True) ∨ False) ∧ ((True ∧ (p4 → p3)) → True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207949109372144219226195252925 : (((p2 → (p4 ∧ p5)) ∧ (p1 ∧ p4)) → ((((True → False) ∧ (p4 ∧ (p2 ∧ ((False ∨ (p1 ∧ ((p3 ∧ p4) ∨ False))) → p5)))) ∧ p4) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118563751497524703005131474174 : ((p4 ∨ (((p5 → (False ∨ (((p3 ∨ ((True → ((p2 ∨ True) ∧ p3)) ∧ False)) → p5) → (True ∨ p3)))) ∧ (p1 ∧ p3)) ∧ p3)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619639731473524058159427124 : (((((p2 ∧ (p5 ∧ p3)) ∧ ((p5 ∧ (p1 ∨ p5)) ∧ (p2 ∧ (False → ((p5 → p4) → True))))) → (p3 → False)) ∨ (p3 → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689729174620856168106396831127 : (((((False → (p2 → p2)) ∧ ((((p2 ∧ (p2 ∨ (p3 ∨ p1))) ∧ p4) ∧ p4) ∧ p1)) ∨ ((True ∨ ((p5 ∨ p3) → (True ∨ p1))) → True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_700250800886818394927480898915 : (((((p2 → p2) → ((((p1 → p2) ∧ (p5 ∨ p2)) ∧ p2) → p4)) → (p3 → (((True ∨ (p1 ∨ p5)) → p4) ∨ ((False → p4) → p3)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200282171726520883280526827617 : (((p2 → (False ∧ p4)) → ((p3 → False) ∧ True)) → ((p4 ∨ (p4 → ((p2 → False) ∨ (p1 → p5)))) ∨ (((False ∧ p5) ∧ (True ∧ p5)) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168825792883644842473354083057 : ((p3 ∨ ((((((False ∧ True) ∧ ((False ∨ p4) ∧ p1)) ∨ (p1 ∧ p4)) ∨ p2) ∨ p3) ∧ p2)) → ((p3 ∧ (p4 → (p3 ∨ False))) ∨ (p5 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Conjunctions on the left can always be decomposed.
          let h12 := h10.left
          let h13 := h10.right
          -- False on the left can always be used.
          apply False.elim h12
        case inr h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h17
          -- One of the premise coincides with the conclusion.
          exact h6
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230839288154814751654743889822 : (((p1 ∧ True) ∨ p3) → (((p4 ∨ True) ∨ True) → (p5 ∨ (((p1 → (p5 → ((True ∨ True) → False))) ∧ (False → ((p4 ∧ p5) ∧ False))) ∨ True)))) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53850501036579594981400994710 : (((((p4 → p3) ∨ p1) ∧ (p1 → (p3 → (True → p5)))) ∨ ((p5 ∧ p1) → (((p3 ∨ p2) ∧ (p1 ∨ (True ∨ (p1 ∨ p3)))) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325760611647168745635916232408 : (p5 ∨ (p2 ∨ (((p2 → p5) ∨ (p4 → (p4 ∨ p3))) → (((p2 ∧ p3) → (False ∧ p5)) ∨ ((p5 ∨ (p2 ∨ (p4 ∧ p2))) ∨ (p1 → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301051517163582880835404187928 : (False ∨ ((((p2 ∨ p3) ∧ ((p1 ∧ True) → False)) ∧ (False → p3)) ∨ ((p4 → (p2 ∨ True)) ∨ (False ∧ (((False → False) ∧ p1) ∧ (p5 ∨ p3)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205784371801381192010631438061 : (((True ∨ p3) → ((p2 → False) → p5)) ∨ ((p3 ∨ ((((p2 ∧ (p2 ∨ True)) ∧ p4) ∨ p1) ∧ (p2 ∨ (((p4 ∧ p2) ∨ p5) ∧ p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691591230984492902673846845301 : ((((p2 ∧ (((True ∧ ((p1 ∧ p2) → p3)) ∧ ((p1 → p5) ∧ (p3 → p2))) ∨ False)) → ((p2 ∧ (p4 ∨ ((p1 ∨ p2) → p3))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65514666366743189702841363188 : ((p3 ∨ (p1 ∨ (((p2 ∧ p4) ∧ (((p5 ∨ p1) ∨ False) → ((p4 ∧ (p4 ∨ (True → (p5 → p2)))) → ((False ∨ p4) ∧ p4)))) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307712796899485662179742556751 : (p1 ∨ (p2 → (p4 ∨ (((((True → (p4 → p5)) → False) ∨ True) ∧ (((p4 ∨ ((p3 ∧ p5) ∨ (p2 → p3))) → (p5 → p3)) ∨ p2)) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722307271687434522951406160518 : (((((p1 ∧ p2) ∧ False) ∧ (((p3 ∨ ((p5 ∧ p5) → ((p4 ∨ p2) → p2))) → False) ∨ (p5 → (True → (True ∨ (p1 ∨ (p4 → p1))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115425214538772679929584033166 : (((((p1 ∨ (p4 ∧ (p2 ∧ p3))) → p2) ∨ False) ∨ ((((p3 ∨ (p5 → p2)) ∨ (p1 → (False ∨ p4))) ∧ p1) ∧ (True → p1))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703860467354557550098403049638 : ((((((((p3 ∨ p2) ∧ p4) ∧ p2) → (p2 → p5)) ∨ p5) → (p4 → (((p3 ∨ p1) ∧ (p1 ∧ p5)) ∨ (False ∨ ((p4 ∨ p1) ∨ p4))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116148802116448677635249262730 : (((False ∨ (p5 ∨ False)) ∧ (((p3 ∧ (p5 → p2)) ∧ ((p5 ∨ ((p1 ∨ p1) ∧ (p2 → p2))) ∧ True)) ∨ (p2 ∨ (p2 ∨ p3)))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590636908936547242267841587566 : (((((p3 ∧ ((((p2 ∨ (p5 ∧ ((p5 → (p2 ∧ (((True ∧ p4) ∨ False) ∨ False))) ∨ p5))) ∨ (False → p1)) → p2) ∨ p3)) → p1) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63170971447132794105527251109 : ((p5 ∧ ((((((((False ∧ p4) ∧ (p5 → p3)) ∨ ((p2 ∨ ((p2 ∧ p4) ∨ p2)) ∧ p3)) ∧ p2) ∨ True) → False) ∧ p3) → (p1 → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38897867376591462609815182955 : (((((p4 → p5) → p4) ∨ (True → ((p4 ∨ (p2 ∨ p4)) ∨ ((True → p1) → ((p4 → (p4 → (False → (p4 → p4)))) → False))))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37315025287257085057512242490 : ((((p4 → (((p1 → p2) ∧ (False ∨ (((p1 ∧ False) ∨ (((True → ((True ∧ False) → p2)) ∧ True) ∨ p4)) ∧ p5))) → p3)) ∧ p2) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300794538030019748237584815307 : (False ∨ ((p5 ∧ ((p1 → ((p2 ∨ p3) ∨ (((p2 ∧ p1) ∧ p4) ∨ p4))) → (p5 ∧ p1))) ∨ ((p5 ∨ True) ∨ (p3 ∧ ((p1 ∨ p4) → False))))) := by
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
theorem thm_5_vars_660444275421038416549513036471 : (((((((((True ∨ p1) ∨ ((True → ((True → p4) ∨ (p1 → (p4 ∧ p4)))) → False)) ∧ p1) ∨ (p2 ∨ p4)) ∧ p3) → p1) → (p5 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165152047446268250228508166641 : ((((True ∨ (((p2 → (p1 → False)) ∨ p4) ∨ p4)) → (p1 → (p5 ∧ p5))) ∧ (p3 ∨ p4)) ∨ (p1 ∨ (p1 → (p1 ∨ (True → (p4 ∧ p2)))))) := by
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
theorem thm_5_vars_263147622307541258773626435775 : (True ∧ (((p3 ∧ p2) → (p5 → ((p4 ∧ (p4 ∨ (p5 ∧ (((p4 ∧ True) ∧ p4) ∧ False)))) ∨ (True ∨ (p4 ∨ (p5 ∨ p5)))))) ∨ (p5 → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183996230331845610869418439275 : ((((p1 ∨ (p5 ∨ (((p3 ∨ p5) ∧ p2) ∨ p3))) ∧ p5) ∨ p1) ∨ ((False → (p2 → True)) ∧ ((p3 ∨ True) ∨ (p1 → (p5 ∨ (False ∧ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596156522844074209070666034128 : ((((((True → ((p2 ∨ p4) ∧ (p5 ∧ p1))) ∧ p1) ∧ ((True ∧ p2) ∧ (p4 → (p5 ∧ ((p3 → (p2 ∨ (p3 ∨ p3))) ∨ p2))))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181986131170979939075378047711 : (((((p3 → (False ∨ p2)) ∨ ((p1 ∨ p3) ∨ p1)) → p3) ∨ True) ∧ ((((p3 → p3) → True) ∧ True) ∧ ((False → ((False → p4) ∧ False)) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797461401183716643957516352265 : (((p1 → ((True → (((True ∧ p5) ∨ ((((True → (p4 ∧ (p4 ∨ (p4 → p2)))) ∨ p3) ∨ p4) ∨ (True ∧ (p2 ∨ False)))) ∨ False)) ∨ p1)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_60316200511257527555573349072 : (((p1 → p4) → (p3 ∨ ((((False → (p2 → (p2 → p5))) ∧ (p5 ∧ (p4 → p3))) → (False ∨ p1)) ∨ (False → ((p3 ∨ p4) ∨ p5))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160803382706538482847171647137 : (((p4 ∧ ((p3 ∨ (p5 → True)) → p4)) ∨ (((p1 ∨ p3) → (False → ((p3 ∨ True) ∧ p1))) ∨ p3)) → (((p2 → False) ∨ False) ∨ (True ∨ p4))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797240900149487378551819756120 : (((p1 → ((((True ∧ ((True ∧ p5) ∧ (((p2 ∨ ((p1 ∧ p3) ∨ p4)) ∨ True) → (p3 ∧ (p2 ∧ (True ∨ p3)))))) ∨ True) ∨ p5) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_785543500100697748018768595156 : (((p4 ∨ ((p2 ∨ ((((((((True ∧ p1) → (p5 ∧ p4)) ∨ p5) ∧ p2) ∧ (p3 ∨ (p5 ∧ (p2 → True)))) → p1) ∨ p2) ∨ True)) ∨ False)) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178205288416898181671621390253 : (((p1 ∨ (True ∨ (((p4 → p3) → (p5 ∧ (p1 → p1))) → True))) → p4) ∨ ((((True ∨ (((p1 ∧ p4) ∧ False) → p5)) ∨ p1) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300789981338236504689084791864 : (False ∨ (((p4 ∧ p3) ∨ ((p2 ∨ p4) → (((p1 ∨ False) ∨ ((p5 → p4) ∨ p5)) → False))) ∨ (p4 → ((((False ∧ p5) → p4) ∨ p4) ∨ p1)))) := by
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
theorem thm_5_vars_136273593033175518480259817153 : (((((True ∧ p5) ∨ p5) ∧ (p4 ∨ p4)) → (((p1 ∧ (((((p1 ∨ p1) → True) ∨ p4) ∨ True) ∧ p4)) ∧ True) → False)) ∨ (True ∧ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115128351875669442709549127331 : ((((p2 ∨ (p3 → (p5 ∧ False))) ∨ ((p4 ∨ (p4 ∨ p4)) ∧ True)) → (True → (((True → p4) ∧ ((p1 → p3) ∧ p4)) ∨ True))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228275747826325839788589444641 : ((p5 ∧ (p5 → p4)) ∨ (((((False ∧ (p5 ∧ (((False ∧ p2) ∧ p5) → (p1 ∧ True)))) ∧ p1) ∨ p3) ∨ (False ∨ p1)) ∨ (p5 → (False → False)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340871193962488646332551644405 : (p2 → (((p4 ∨ ((((p5 ∧ ((True → False) ∧ ((p3 ∧ p2) ∨ p1))) ∨ p5) ∧ True) ∨ (p2 ∧ p4))) → ((p1 ∧ (p5 ∧ False)) ∧ p2)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50566262842193250964977657800 : (((((False ∧ (p4 ∨ (((True ∨ (p1 → ((p2 ∨ False) ∨ False))) → (True ∨ p2)) ∨ p5))) → p4) → p1) → (((p3 ∨ p2) → p5) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_770069420820883210133561026271 : (((p5 ∧ (p3 → (p2 ∨ (((p3 ∧ p4) ∨ ((p4 → ((((p2 ∧ p4) → p3) ∧ p5) ∨ p1)) → p5)) → (((True ∧ False) → p5) ∧ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42706342493963576508397338322 : (((p5 ∨ ((p3 ∧ (p2 ∨ p4)) ∧ ((True → (p1 → (False → (True ∨ (p3 → ((p5 → p2) → ((p2 ∧ p5) ∨ p2))))))) ∧ p1))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187321618186593573399401570421 : ((p1 ∧ (p2 → ((((False → p4) ∨ p3) ∨ (p4 → p3)) → True))) → (p5 ∨ (((((p5 ∨ p4) → p2) ∧ p2) ∨ True) ∨ ((p5 → p4) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319182010279042341111903862626 : (p4 ∨ ((p2 ∧ ((((p5 ∨ p3) → (p4 ∧ (p5 ∨ True))) ∧ (p3 ∧ p3)) ∨ ((p4 ∧ True) → p2))) ∨ ((p4 → (p4 → (p5 ∨ p3))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326305299194046675230238623384 : (p5 ∨ (p4 → ((False ∨ ((p1 ∨ (False → (p3 → False))) → p3)) ∨ (((False ∧ (p1 → (p2 → p3))) → (True → p1)) ∨ (True → (p1 → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185933943693657024413738630275 : ((((True ∧ (True ∨ p5)) → (((p1 ∧ p2) ∨ p4) ∨ True)) ∧ True) → (p2 → (((p5 → p3) ∨ (p1 ∨ (p4 ∨ False))) → (False ∨ (p1 ∨ p2))))) := by
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
    let h5 := h1.left
    let h6 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h1.left
      let h10 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h1.left
        let h14 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h15 =>
        -- False on the left can always be used.
        apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60163638720967498949356195001 : (((p4 ∨ p5) → (False ∧ ((p5 ∨ ((p3 → False) ∧ p4)) → (((p2 ∧ (p4 → ((p2 → (p3 ∨ p2)) ∨ True))) ∨ (True ∨ p1)) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304075175363976506602240435513 : (p1 ∨ ((p3 ∨ (((False ∨ ((((False → False) ∨ p5) ∧ (True ∧ (False ∨ p2))) ∨ True)) ∧ ((p4 ∨ p5) → p2)) ∨ (p4 → (True ∨ p1)))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_666832893343505554562087399229 : (((((p2 ∧ ((p2 ∧ p2) → ((p2 ∧ p1) → p3))) → ((((((p3 → p1) ∧ p4) ∨ p1) ∨ p2) ∨ True) ∨ p2)) ∧ (True ∨ (False ∧ p5))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167934352373795061359934818900 : ((((p1 ∨ p5) ∨ (True → (p3 ∨ (p1 → p2)))) ∨ ((p3 ∨ ((p5 ∧ p5) → p5)) → p3)) → (((p2 → p4) ∧ p1) ∨ ((p4 ∧ p3) → p3))) := by
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
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h17
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49736923126144768051621839882 : (((p3 ∧ ((p2 → (((p1 ∨ (p4 ∧ ((p2 ∨ p4) ∨ (p3 ∨ False)))) ∧ p4) → (True ∧ (True ∧ p4)))) ∨ p4)) → ((p5 ∧ True) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179889675524079755654356015394 : (((((p5 ∨ True) ∧ ((p4 → ((p2 ∨ False) ∧ p5)) ∧ p2)) ∧ True) ∨ p1) → (((p2 ∨ p4) ∨ (p2 ∨ (p3 ∨ ((p2 ∧ p3) ∨ p5)))) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h6.left
      let h12 := h6.right
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
theorem thm_5_vars_349347110068443245991962401977 : (p3 → (p3 → ((p1 ∨ ((((p1 ∧ ((p4 ∨ (p1 ∨ p2)) → (p4 → True))) ∨ True) ∧ p2) ∧ (((False ∨ p4) ∧ False) ∧ True))) ∨ (p1 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165397411518053773597709032283 : (((p3 ∨ (p1 ∧ (((p3 ∧ True) ∨ (p3 ∨ p4)) ∧ (False ∨ p2)))) ∨ ((False → p1) ∨ p3)) ∨ (True ∨ ((p2 ∨ p1) ∧ ((p4 ∧ False) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340754105807505971932937361457 : (p2 → ((((p4 → p4) ∧ ((p5 → (p4 ∧ (p5 ∧ p1))) ∧ (((p3 ∧ ((p5 ∨ p3) ∧ (p2 → p4))) ∧ (True ∨ True)) ∧ p2))) ∨ p4) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638560159194624480012351140345 : (((((True ∧ ((False → (p4 → p5)) ∧ False)) ∨ (True ∧ (((p1 ∨ p2) ∧ (False ∧ (((False ∨ p4) ∧ False) ∧ p2))) → (p2 ∧ p3)))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151163824717729601669233366353 : (((((p3 ∨ ((p3 → p4) → (p5 ∧ (p3 → (p4 ∨ p4))))) ∨ False) ∧ ((p1 ∧ (p3 ∧ p1)) → p2)) → p2) → (((False ∨ p4) ∧ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234719722543710622994687936652 : ((p4 → (p3 ∨ p4)) → (((((p1 ∨ (p5 ∧ (p2 ∨ (p3 ∧ p1)))) ∨ (p2 ∨ p5)) → True) → ((p5 ∧ (p4 → (p2 → p1))) ∧ p4)) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((p1 ∨ (p5 ∧ (p2 ∨ (p3 ∧ p1)))) ∨ (p2 ∨ p5)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46568574979398445463021363881 : (((True ∧ ((((((p1 ∧ ((p2 ∨ p4) ∨ (p3 → p4))) ∧ p5) ∧ (p5 ∧ False)) → (True → (p3 ∧ False))) → p3) ∧ p4)) ∧ (p5 ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53206261684731771355488885760 : ((((p3 ∨ ((p2 → p2) → ((p4 ∨ p1) ∧ p2))) → (p5 ∨ p5)) ∨ ((((p3 ∨ (True ∧ p2)) ∨ ((False ∨ p2) ∧ False)) ∧ p1) → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174000281640500957315150960271 : ((((p1 → p3) → ((((p2 ∧ p1) ∨ False) ∧ (p4 ∧ p1)) ∧ (p1 ∨ p3))) → p1) → (p4 → (p4 ∨ (p2 → ((True ∨ (p1 ∧ p3)) ∧ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173898057563861100426901933283 : ((((((p5 ∨ p1) → ((p3 → (False ∨ p2)) ∧ (p4 ∧ p2))) ∧ p1) → p4) → False) → ((p3 ∧ (p5 ∨ (True → (p5 ∧ p1)))) → (p2 ∧ False))) := by
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
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : ((((p5 ∨ p1) → ((p3 → (False ∨ p2)) ∧ (p4 ∧ p2))) ∧ p1) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h10 : (p5 ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h11 := h8 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h14 := h1 h6
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h16 : ((((p5 ∨ p1) → ((p3 → (False ∨ p2)) ∧ (p4 ∧ p2))) ∧ p1) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h17
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h20 : (p5 ∨ p1) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h21 := h18 h20
      -- We need to get the right conjuct of h21 based on <expert-advice>.
      let h22 := h21.right
      -- We need to get the left conjuct of h22 based on <expert-advice>.
      let h23 := h22.left
      -- One of the premise coincides with the conclusion.
      exact h23
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h24 := h1 h16
    -- False on the left can always be used.
    apply False.elim h24
  -- Conjunctions on the left can always be decomposed.
  let h25 := h2.left
  let h26 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h26
  case inl h27 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h28 : ((((p5 ∨ p1) → ((p3 → (False ∨ p2)) ∧ (p4 ∧ p2))) ∧ p1) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h29
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
      have h32 : (p5 ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h27
      -- We have shown the premise of h30, we can now drive its conclusion.
      let h33 := h30 h32
      -- We need to get the right conjuct of h33 based on <expert-advice>.
      let h34 := h33.right
      -- We need to get the left conjuct of h34 based on <expert-advice>.
      let h35 := h34.left
      -- One of the premise coincides with the conclusion.
      exact h35
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h36 := h1 h28
    -- False on the left can always be used.
    apply False.elim h36
  case inr h37 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h38 : ((((p5 ∨ p1) → ((p3 → (False ∨ p2)) ∧ (p4 ∧ p2))) ∧ p1) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h39
      -- Conjunctions on the left can always be decomposed.
      let h40 := h39.left
      let h41 := h39.right
      -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
      have h42 : (p5 ∨ p1) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h41
      -- We have shown the premise of h40, we can now drive its conclusion.
      let h43 := h40 h42
      -- We need to get the right conjuct of h43 based on <expert-advice>.
      let h44 := h43.right
      -- We need to get the left conjuct of h44 based on <expert-advice>.
      let h45 := h44.left
      -- One of the premise coincides with the conclusion.
      exact h45
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h46 := h1 h38
    -- False on the left can always be used.
    apply False.elim h46



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64696808175217372214179564830 : ((p1 ∨ (True → (True → (((p2 → p2) → (((((p3 ∧ p1) ∨ p4) ∧ (p4 → True)) → p3) ∧ (False ∨ (p1 → (p5 → True))))) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2642639289146046483278239809 : ((((p1 ∧ (p5 ∨ p3)) ∨ False) ∧ p1) ∨ ((p1 ∧ (((p5 ∨ True) ∧ p2) → p4)) ∨ (p4 → (False → (p4 ∨ (p2 ∨ (p4 ∨ p1))))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115131612495988343685880021823 : (((((p3 → p3) ∨ p2) ∨ ((p5 ∨ ((p3 → p4) → True)) → p5)) → (True ∧ (((True → p2) ∧ (p3 → (p4 ∨ True))) ∨ p1))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702536048820148146381753714018 : (((((((p3 ∨ (p3 ∨ p2)) → p5) ∧ (True ∨ p4)) → p5) ∨ (((p1 ∨ (p5 ∧ p3)) ∧ p1) → (((False ∧ (False ∧ p5)) ∧ p3) → False))) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119435040957074360576445992926 : ((p4 → (((True ∨ (((((p4 → p3) → (p2 ∧ True)) ∧ (p1 ∨ p2)) → p1) → p5)) → p5) ∧ (((p3 → True) → True) ∨ p4))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343389543022406367643997617152 : (p2 → ((p1 ∧ p3) ∨ (((((p4 ∧ ((p1 ∨ (p2 ∧ (p5 → (False ∧ p5)))) ∧ p3)) ∨ p2) ∧ (p3 ∨ (p3 ∨ True))) ∨ (p2 → False)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_388269848470660937860445096241 : ((((((p3 ∧ p2) ∨ (((p5 ∨ (p5 ∨ p4)) ∨ (p4 ∨ p4)) ∨ (((True ∨ p5) ∧ True) ∨ p2))) ∨ (((True ∨ p4) → False) → p2)) ∨ False) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305868488171421664924191833947 : (p1 ∨ ((((p3 ∧ (p5 → p3)) ∧ True) → p2) ∨ (p1 ∨ (True ∧ (((((p1 ∧ (p1 ∧ p1)) ∨ (p5 ∧ (p3 → True))) → p2) ∨ True) ∨ p2))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133929909306977877451163587012 : (((True → ((((p3 ∨ ((((True → False) → (True ∧ False)) ∧ ((p4 → p1) ∨ True)) ∧ p1)) ∧ p4) ∨ False) ∨ p2)) ∧ p2) ∨ ((True ∧ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300504310554361157575912154551 : (False ∨ ((((p3 ∧ (p4 ∨ (p1 ∧ p5))) ∨ (((p4 → True) ∧ True) ∧ True)) ∨ ((True ∧ (p4 ∨ True)) ∧ p2)) ∧ ((p4 ∨ False) → (p1 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68844777968051297385800374020 : ((p4 → ((p4 ∧ False) ∨ (False ∨ (((p2 ∧ p4) → (p5 → (True ∨ (p4 ∨ p4)))) → ((p3 ∧ (False ∨ p2)) ∨ ((True ∧ p4) ∧ True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53533999438181584872494060221 : ((((((p4 ∨ (p3 ∨ (p1 → True))) ∧ p2) ∧ p3) ∧ False) ∧ (((True → (((p3 ∧ False) ∨ p3) ∧ p3)) ∨ (p5 → (p5 ∨ p1))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59465090188487260429551085617 : (((p1 → False) ∨ (((False ∧ ((True → p4) → (p1 ∧ p5))) ∨ p2) ∧ (((False ∧ (p1 ∨ (p5 ∨ p5))) ∨ p4) → (p5 → (False → p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66835798899798985657365816821 : ((True → (p2 → ((p1 ∧ ((True ∧ False) ∧ (((p2 ∨ p1) ∨ p1) → (((((False ∨ p5) ∨ True) ∧ p1) ∨ p3) ∨ False)))) ∧ (p3 → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118313368414533258150792784668 : ((p1 ∨ (True → (((p3 ∧ ((False ∧ ((True → (p3 ∧ p1)) → False)) → p5)) → ((p5 ∨ (p5 → p4)) ∨ (p5 ∧ p5))) ∨ p1))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639714887956310978635124447111 : (((((True → (p4 → p3)) ∧ ((((p5 → p1) → p3) → (True → (p3 → (p3 → ((p2 ∧ p3) → (p4 ∨ p2)))))) ∧ (p4 ∧ p5))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712839354713701572518594934361 : (((((False ∨ p3) → (p1 ∨ (p5 ∨ p1))) ∨ ((p5 ∨ ((p2 ∨ (False ∧ (p5 ∨ False))) ∧ ((((p1 ∨ p4) → p3) ∨ True) → p1))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259220235168983381986041298403 : ((False → False) → (((p3 → False) ∨ True) → (((((p1 → False) → (p4 → p5)) ∧ (p4 ∧ False)) → p5) → ((p2 → p5) → ((p3 ∧ p2) → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h8 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h12 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h13 := h4 h12
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120907799368493571063652641321 : ((((((False ∨ (False ∧ p1)) ∨ False) ∧ True) → ((((p5 ∧ p5) → (p5 ∧ (False ∧ p2))) ∧ (False → (True ∨ p3))) ∨ p1)) ∨ False) → (p2 → p2)) := by
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
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224556589995454489419875827956 : ((p2 → (p2 ∨ p1)) ∧ ((((p2 ∧ p3) ∨ (False ∧ p5)) ∧ p1) ∨ ((p5 → ((p5 → (p1 → False)) ∧ p2)) → (p1 → ((False ∨ p2) ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41075207686329945319771287811 : ((((p1 → ((False → False) ∧ (p1 ∨ ((p4 ∨ (p3 → ((p4 ∨ ((True ∨ p3) → p5)) → True))) ∨ (False ∨ p5))))) → (p5 ∨ True)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_867535442773384590484913986 : ((p5 ∨ ((((p4 ∨ (True → p1)) ∨ ((True → p4) ∨ (p4 ∨ (p1 → True)))) ∧ (False ∧ (((p3 → p1) ∨ p4) ∨ True))) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113530680709181196603702056780 : ((((True ∨ (((p5 ∨ p2) ∨ p5) ∧ p5)) ∧ (((p2 ∨ (p1 ∨ (False ∨ p4))) ∨ ((True ∨ p5) → p5)) → p1)) ∨ (p2 → p2)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725507734375603830268455200888 : (((((True ∧ p5) ∧ p1) ∨ ((p4 ∧ p2) ∧ (((((True ∧ ((p1 ∧ p5) ∧ p4)) ∧ True) → False) ∨ (p5 → (p3 ∨ (p2 ∧ p4)))) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669409926910404639629731614427 : ((((((p4 ∨ (((p4 ∨ p3) → p1) ∨ ((p5 ∧ True) ∧ ((p5 ∧ True) → p3)))) → (False ∧ False)) ∨ (True ∨ False)) ∨ (p5 ∨ (p1 ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704945123920289772251462146444 : ((((p5 ∨ ((p4 → p4) ∧ ((p3 ∨ p1) ∧ (p5 ∨ p3)))) → ((((((p2 ∧ False) ∨ p4) ∨ (False → (False ∨ p3))) ∧ False) ∨ True) ∨ False)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



