variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257169043865781882823936463433 : ((p2 ∨ p1) → (p2 ∨ ((((((p2 ∧ ((p4 ∧ True) → (p5 ∧ ((p2 ∧ (p1 ∧ p3)) ∨ True)))) ∨ p2) ∧ p5) ∧ p2) ∨ p3) ∨ (True ∨ False)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174801055220050439332025332396 : (((True → p2) ∧ ((p4 ∨ (p3 ∨ ((((p4 → p1) → p1) ∧ p3) → p1))) ∧ p3)) → (True ∧ ((p4 ∨ ((p4 ∨ p1) ∧ p1)) → (p2 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h10 := h4 h9
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h13 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h14 := h4 h13
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h17 := h4 h16
        -- One of the premise coincides with the conclusion.
        exact h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h1.left
      let h23 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h26 =>
        -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
        have h27 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h22, we can now drive its conclusion.
        let h28 := h22 h27
        -- One of the premise coincides with the conclusion.
        exact h28
      case inr h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
          have h31 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h22, we can now drive its conclusion.
          let h32 := h22 h31
          -- One of the premise coincides with the conclusion.
          exact h32
        case inr h33 =>
          -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
          have h34 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h22, we can now drive its conclusion.
          let h35 := h22 h34
          -- One of the premise coincides with the conclusion.
          exact h35
    case inr h36 =>
      -- Conjunctions on the left can always be decomposed.
      let h37 := h1.left
      let h38 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h39 := h38.left
      let h40 := h38.right
      -- Disjunctions on the left can always be decomposed.
      cases h39
      case inl h41 =>
        -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
        have h42 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h37, we can now drive its conclusion.
        let h43 := h37 h42
        -- One of the premise coincides with the conclusion.
        exact h43
      case inr h44 =>
        -- Disjunctions on the left can always be decomposed.
        cases h44
        case inl h45 =>
          -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
          have h46 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h37, we can now drive its conclusion.
          let h47 := h37 h46
          -- One of the premise coincides with the conclusion.
          exact h47
        case inr h48 =>
          -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
          have h49 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h37, we can now drive its conclusion.
          let h50 := h37 h49
          -- One of the premise coincides with the conclusion.
          exact h50
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59022394337796101482136918884 : (((p3 ∧ p5) ∨ (p3 ∧ (True → ((((True → (p1 ∧ False)) → (p1 ∨ (False ∨ ((p4 → p4) ∨ (p4 → (p1 ∨ p4)))))) → p1) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209048300211409941869043298550 : ((p1 ∨ (((p3 ∨ p2) ∧ False) → p2)) → ((p1 → ((((False ∨ True) ∧ p4) ∧ p5) ∧ p3)) ∨ (p2 ∨ (p1 ∨ (p3 ∨ ((False → p1) ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
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
    intro h4
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64082627683622015606830992041 : ((False ∨ (((((p4 ∨ p3) → p2) → ((True → p3) ∨ True)) → (p4 ∧ (p3 → p1))) → ((((p2 ∧ (False → p4)) → p3) → p5) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164752075444701434872853857431 : (((((p5 ∨ p1) ∧ (p1 → ((True ∨ (p2 ∧ (p4 → p4))) ∧ False))) → (p3 → p4)) ∨ True) ∨ ((((False → (p4 ∧ p1)) ∧ False) ∨ p5) ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684641034108121433678074477262 : ((((((True → True) ∧ p2) ∨ (((False → p1) ∧ (p4 ∧ (p4 ∧ (False ∨ (p3 ∨ p5))))) ∧ p5)) ∨ (True ∨ ((p3 ∧ False) → (p2 ∧ p4)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_618845459606487354443081486740 : (((((p1 ∨ (p3 ∨ p2)) ∧ ((p1 ∨ (p1 ∨ (True → ((True ∨ p4) ∧ p4)))) ∨ ((True ∨ ((True ∧ (p4 → p3)) ∨ p2)) ∨ p5))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136209985654723630134767794557 : (((p2 → ((False ∧ (True ∨ False)) → True)) ∧ (((((True ∨ ((p4 ∧ p3) → p1)) → (False ∧ p5)) ∧ p5) ∧ p5) ∨ True)) ∨ ((p2 → p2) → p2)) := by
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
theorem thm_5_vars_751471278852806200473881183353 : (((True ∧ ((p5 → p3) → ((((p4 ∧ p3) → p1) ∨ p4) ∧ (p5 ∨ (((((p2 ∨ False) ∨ p1) ∨ ((p1 ∨ True) ∧ p2)) ∧ p1) ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198285196364632873199371481125 : ((False ∧ (True → ((p4 ∨ (False ∧ False)) ∨ p4))) ∨ (((((p5 ∧ p4) → p4) ∨ p5) ∧ (p3 ∨ True)) ∧ ((p3 ∧ ((p2 ∧ p4) ∨ p2)) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54724280103663528384179037227 : (((((True → p3) → p2) ∧ (p2 ∧ (p5 ∧ p2))) → (((p3 → (p2 ∧ p5)) ∨ (p2 ∨ (True → ((p1 ∨ True) → False)))) ∧ (p5 → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620376780338302987243802272610 : (((((p3 ∨ p2) ∨ (p5 → ((p4 ∨ p3) ∨ (True → (True → (((((True ∨ p2) → True) ∨ (p5 ∨ (p5 ∧ p1))) ∨ p5) ∧ p2)))))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226811447026289312835136916432 : (((p3 ∧ p4) → p1) ∨ ((((p1 → False) → (p4 ∨ (p1 → p4))) ∧ p4) → (((p1 → p4) ∧ p2) → (p1 ∨ (p4 → ((p2 ∧ p4) ∨ p4)))))) := by
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
  let h5 := h1.left
  let h6 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_919262295425577659491054564844 : ((((((p5 ∨ (p2 ∧ p3)) → p4) ∧ (((p5 → p2) ∨ (p4 ∨ True)) → False)) ∧ ((p1 → (((True ∨ p5) ∧ False) ∨ p3)) ∧ (p4 ∨ True))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  cases h7
  case inl h8 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h9 : ((p5 → p2) ∨ (p4 ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h12 : ((p5 → p2) ∨ (p4 ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h13 := h5 h12
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160257099595029760181371651568 : (((p3 ∧ ((False → ((p4 → (True → (p5 → p5))) → ((p5 → p5) ∧ p1))) ∧ p4)) ∨ (True ∨ p3)) → (((True → False) ∨ p2) ∨ (True ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248395007906012089318827885941 : ((p2 ∨ p4) ∨ ((p4 ∧ (((((p1 ∨ ((False → (p3 ∨ p5)) ∧ p1)) ∧ p4) ∨ (False ∧ (p4 → p3))) ∧ p4) ∨ p2)) ∨ ((True ∨ p1) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119285463894743866591849435296 : ((p3 → (((False ∨ ((p5 → ((True ∧ p1) ∧ p4)) ∨ False)) ∧ ((p4 ∧ p3) → (True ∧ (p2 → ((p3 ∨ p1) → False))))) ∨ p3)) ∨ (True → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66656594523211742855019885895 : ((True → ((((((p3 ∧ p3) ∧ p2) ∨ p4) ∧ p3) ∨ p4) ∨ ((((False ∨ True) → p2) ∧ (p5 ∨ (p1 → (p4 → p5)))) → (p4 ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609765673698804563896070933832 : (((((p4 ∨ (p2 → (((((p2 ∧ (p3 → (p4 → p5))) ∨ (p4 ∧ p4)) ∧ True) → (p1 ∨ (True ∧ p3))) ∨ (False ∨ False)))) ∨ p3) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_190698880022189667075609393145 : ((((((p3 → False) ∧ p4) → False) ∨ p5) ∧ (p3 ∧ p2)) ∨ (True ∧ ((p2 → (p3 ∨ ((p2 ∨ ((p1 ∧ p1) → (True ∨ p3))) ∨ p5))) ∨ False))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50709814952483425327390057655 : ((((p2 → p2) ∧ ((p2 → ((((p4 ∨ ((p4 ∨ p5) → True)) ∨ True) ∧ p4) ∧ False)) ∧ (p2 ∨ True))) → ((False → (True ∨ True)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219083198829473355353413995914 : ((p5 ∧ (p4 → (True → p1))) → ((p4 ∨ (False ∧ ((p2 → p3) ∧ ((p2 ∨ p1) ∨ (((p3 ∨ p3) ∧ (p4 ∨ p1)) ∨ (False ∨ p4)))))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257828203891292844576354622952 : ((p3 ∨ p5) → ((p5 ∨ False) → (((((True → (p5 → p3)) ∨ True) ∨ (p1 → p4)) → (((True ∧ p3) ∧ (False ∨ False)) ∧ p1)) → (p5 ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h10 : (((True → (p5 → p3)) ∨ True) ∨ (p1 → p4)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h11 := h3 h10
      -- We need to get the left conjuct of h11 based on <expert-advice>.
      let h12 := h11.left
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h17 : (((True → (p5 → p3)) ∨ True) ∨ (p1 → p4)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h18 := h3 h17
      -- We need to get the left conjuct of h18 based on <expert-advice>.
      let h19 := h18.left
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- False on the left can always be used.
        apply False.elim h22
  case inr h23 =>
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60245578954455048052263911464 : (((False → True) → (((True ∧ ((p1 → (True ∧ ((True ∧ (True ∨ p2)) ∨ p5))) ∧ (((p3 ∧ p3) ∨ True) → p1))) → p2) ∨ (p1 → True))) ∨ p1) := by
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
theorem thm_5_vars_166912054617368325451511036327 : (((((False → p2) ∧ ((p4 → False) → p2)) → ((p3 ∧ (p4 ∧ (p4 ∧ False))) ∧ False)) ∧ p3) → (((p2 ∨ p1) ∨ (p3 ∨ (False ∧ p2))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608900353365394447585665598203 : ((((((p4 ∧ ((p2 → (((((p4 → False) → p1) → True) ∧ p3) → False)) ∨ p3)) ∧ (p2 ∨ (((True ∨ p5) ∨ p5) → False))) ∨ p1) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160433248139180082967227276993 : (((p2 ∨ ((p4 ∨ (True ∧ p1)) → (p2 → (((False ∨ p1) → True) → p2)))) ∨ ((p1 ∧ p2) ∧ p1)) → ((p5 ∨ p4) ∨ (False → (True ∨ False)))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690164496385653657991505692124 : ((((p2 ∨ ((p2 → (((p2 ∨ p3) ∧ p5) ∧ False)) → (((True ∧ p4) ∨ p5) → p3))) ∨ ((((p1 → True) ∧ p5) ∨ (False → p3)) ∨ p2)) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227995810168707549885396063920 : ((p3 ∧ (p4 ∨ p5)) ∨ (p5 ∨ ((False ∨ (p5 → (p5 → (False → (p1 → (True ∨ ((True → (False → (p2 → (p2 ∨ p1)))) ∨ False))))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61718874661772213435462782002 : ((p1 ∧ (True → ((((((p4 → False) ∧ False) → False) → p1) ∧ p5) ∨ (False ∧ ((p1 ∧ p1) ∧ (((True ∧ True) ∨ False) ∧ (p5 ∨ p3))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172627211098960883701291236877 : (((p2 ∧ p5) ∧ ((((False → (False ∧ p5)) → p2) ∧ True) ∨ (p2 ∨ (p1 ∨ False)))) ∨ (False → ((((p5 ∨ p1) ∧ p5) ∨ p5) → (True ∧ p5)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h1
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h1
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767278718421479331549289883747 : (((p5 ∧ ((((((True ∨ (((p4 → p3) → False) ∧ p1)) ∧ p4) → False) ∨ ((True ∨ False) ∨ (p5 ∨ p4))) ∧ ((False → p3) ∧ p2)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716635251762096036127546671624 : (((((p4 ∧ False) → (p1 → p3)) ∧ (((False ∧ p2) ∨ ((((p1 → p4) → (False → True)) ∧ p3) ∧ p4)) ∧ (p1 ∨ ((p3 ∨ p3) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712031478598174368464901191975 : ((((((p3 → p5) ∧ (p1 ∧ False)) ∨ p2) ∨ (((True ∨ p5) → (((p3 ∨ p4) ∧ (p5 ∧ True)) ∧ True)) ∨ (p1 ∨ (p3 ∨ (False → p4))))) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215582164754126288327425995800 : ((p5 ∧ (False ∧ (False ∧ False))) ∨ ((p3 → p5) ∨ (True → ((p2 ∨ ((p3 ∧ (p5 → ((p4 ∨ p3) ∨ (p5 ∨ p4)))) → p3)) ∨ (p3 ∧ True))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215970168904363391602853518208 : ((p4 ∨ ((True ∨ p2) → p1)) ∨ (((True → p3) ∧ (p2 ∧ (p4 → (False ∨ True)))) → (((False ∨ True) → p4) → ((p1 ∧ (p5 ∧ True)) → p3)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h12 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h13 := h8 h12
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4116179740384212516636308781 : (p3 ∨ ((p1 ∨ (p1 ∧ p4)) → (False ∨ (p3 ∨ ((p1 ∧ (((p2 → ((p2 ∧ (p4 ∨ p3)) ∨ (p2 ∨ True))) ∨ p2) ∧ p4)) ∨ p1))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654193842805917270020645230442 : ((((((p5 ∧ ((p3 ∨ p1) ∨ (p5 ∨ ((False → (p1 ∧ p5)) ∧ (True → ((p3 ∨ (p1 ∧ p5)) ∧ p2)))))) ∨ True) ∨ p4) ∨ (p2 ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337440378193688038263937511629 : (p1 → (((True → (p1 ∧ (p4 ∧ False))) ∨ ((((p3 ∧ False) ∨ False) ∧ p1) ∧ ((p4 ∨ p2) ∧ ((False ∧ p5) → p5)))) → (p1 ∧ (False ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h13 =>
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h15 := h13 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- False on the left can always be used.
    apply False.elim h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h19.left
    let h22 := h19.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- False on the left can always be used.
      apply False.elim h25
    case inr h26 =>
      -- False on the left can always be used.
      apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43354415185935362458976049359 : ((((((p1 ∧ (p1 ∨ p1)) ∧ (True ∨ (((p3 ∨ p3) ∨ ((False ∨ p2) ∧ (True ∨ (p3 → p1)))) ∨ False))) ∧ (True ∧ p1)) ∨ p1) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767280127131764151777386714640 : (((p5 ∧ (((p4 ∧ (((p1 ∧ (((p5 → (p3 → ((True ∧ p3) ∧ False))) ∨ p3) ∧ p5)) ∧ p5) ∨ p2)) ∧ ((False ∧ False) ∧ p5)) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113604815631650449339630137692 : (((p2 ∨ ((False ∨ (((((True → False) → p1) ∨ (((p2 → p4) ∧ p3) → (True → p3))) → p2) ∧ p1)) ∨ p2)) ∨ (False ∨ p1)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42725614388471809835231733458 : (((True → ((((((((p4 ∨ p5) ∨ ((True ∧ (p5 ∧ (p1 → p3))) ∨ p5)) ∨ True) ∨ p5) ∧ (False → p5)) ∨ False) ∧ p1) ∨ p3)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314279062560524373103883054016 : (p3 ∨ ((p4 ∨ ((((p4 → ((True ∧ (p2 ∧ ((True ∧ (p5 ∧ p1)) ∨ True))) ∨ True)) → (False → p1)) ∧ False) ∨ False)) ∨ (p1 ∨ (True ∨ p3)))) := by
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
theorem thm_5_vars_209485970156860051198003015575 : ((p3 → (p1 ∧ ((True → True) → p2))) → ((((p2 ∧ (((p5 → p5) → True) ∨ ((p1 → False) → p4))) → p2) ∨ (True ∧ False)) ∨ (p4 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308747291759631876793621158917 : (p2 ∨ ((p5 → ((((False → ((p4 ∨ (p4 ∨ ((False ∧ p3) ∧ p5))) ∧ p1)) → ((p4 → p2) ∧ (False → (p3 → p4)))) ∨ p4) ∨ p5)) ∨ p2)) := by
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
theorem thm_5_vars_733369286871593053710435841035 : ((((p4 ∧ True) ∧ ((p2 ∨ p2) ∨ (p1 → (p4 ∨ (((((p2 → False) ∨ (p2 ∨ p5)) ∨ True) ∨ (p3 ∧ (p3 ∧ p5))) ∨ (p2 ∨ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206029253146279694821893935613 : ((p2 ∧ ((p3 → p4) ∧ (p5 → p5))) ∨ ((p1 ∧ (p3 → p3)) → ((((p4 ∧ (((p4 ∧ p3) ∨ p4) → (False ∧ p3))) ∧ p4) → False) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h9 : ((p4 ∧ p3) ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h10 := h6 h9
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212600845872438937715309406948 : ((p5 ∨ (p3 → (p3 ∨ True))) ∧ ((p3 ∨ (((((False ∧ p1) ∨ p5) ∧ (p1 ∧ True)) ∧ ((p1 ∨ True) ∨ (False ∨ p2))) ∧ (False → p1))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148805290405951535297377172897 : ((((((p4 ∧ p4) → p2) → p3) → p1) → ((p2 → (p3 ∧ ((True ∨ False) ∧ ((p1 ∨ p4) ∨ p1)))) → p3)) ∨ ((p5 → p2) → (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590722172803690503416900280053 : (((((True ∨ ((True ∨ (((p3 ∨ ((p2 ∨ p2) → ((p1 ∨ False) → p3))) ∧ False) → p4)) ∨ (p2 ∧ ((p1 → p1) ∨ True)))) → p2) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204707015546091289409322674076 : (((p5 ∨ ((p2 ∧ False) ∨ p5)) ∨ p1) ∨ ((False ∨ True) ∨ ((p5 ∨ p5) ∨ ((p5 → ((p4 ∨ ((p2 ∧ p2) ∧ False)) ∨ (True ∧ False))) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318646224390360538141702780897 : (p4 ∨ ((p4 ∨ (((((p5 → True) ∨ p2) ∧ ((p1 ∨ False) ∧ p1)) ∧ (p4 ∨ p5)) ∧ (((p3 ∨ (p2 ∧ p4)) ∨ True) ∧ p5))) ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313943065271560258769188773211 : (p3 ∨ ((((((True ∧ (True ∨ (p2 ∨ (p4 → (p3 → (p5 ∨ p1)))))) → (p5 → p4)) ∧ (p4 ∨ (p2 ∨ False))) → p2) → p1) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172694823885124731477610058180 : (((p4 ∧ p2) ∨ (((False → p2) → (p4 → (False ∨ (p3 ∨ (True → p1))))) ∨ True)) ∨ ((False → p1) ∧ (p1 ∨ ((p1 ∧ (p5 ∧ p2)) → p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133780578020295967440762745474 : (((((False ∧ p3) → (p3 ∧ p2)) → (((p3 ∧ ((p3 → (p4 ∧ False)) → (p3 ∧ p1))) ∧ p1) ∨ (p2 ∨ p1))) ∧ p2) ∨ (False → (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628315006938310580473110486240 : ((((((p5 ∨ True) → (((p5 ∧ p3) ∨ False) ∧ ((p5 ∨ True) → ((p3 ∨ (((True ∨ p2) ∨ (False → p5)) → False)) ∨ True)))) ∧ p2) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629722402851037546890012065655 : (((((((p5 → (((p4 → ((p5 ∨ p1) ∧ p2)) ∨ p4) → (True ∧ p3))) → p3) ∧ (False ∨ ((False → p1) → (p2 → p1)))) ∨ False) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629359642074773306497121356833 : (((((((p3 ∧ p4) → ((((False ∨ (p2 → (p2 ∧ (p1 ∨ (True ∨ p5))))) ∧ (p2 → (False → True))) ∧ p1) ∧ p5)) → p1) ∨ p5) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153069576774565314251847815079 : ((p3 ∧ (((p4 → (((True → False) ∧ ((p5 ∧ p4) ∧ p2)) ∧ p4)) ∧ p2) ∧ (((p5 → p4) ∨ True) → p4))) → ((True ∨ False) → (p5 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698583636428811444615551751231 : (((((p5 ∧ ((p5 ∨ False) → p5)) → (((p3 → True) → p1) ∧ True)) ∨ ((p3 → ((False → ((False → p5) ∨ p4)) ∧ p5)) → (p3 → True))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_613833737834705212367754059016 : ((((((((p5 → ((p3 → (False ∨ True)) ∨ (p5 → p3))) → (((p2 → False) → p5) ∨ p2)) → p3) ∧ p1) ∨ ((p2 → True) ∨ p3)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_638627053977623015117980759487 : ((((((((p2 → p3) → p3) ∨ p1) ∧ p2) → (False ∨ (True → (p1 ∨ (((True ∨ (((False → p2) ∧ p3) ∨ p2)) ∧ p2) → p5))))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39995899525482852203274544102 : (((p5 → (((((p1 ∧ p1) ∨ False) ∧ ((p3 ∨ False) → (p2 → False))) ∨ (((p5 ∨ (p4 ∨ False)) ∨ False) ∧ p5)) → (p3 ∧ p2))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123899778308286866078529247345 : ((((((((True ∨ p4) ∧ True) ∨ True) ∧ p2) ∧ (p5 → p5)) ∧ p4) ∧ ((p1 → (((p3 ∧ True) ∧ p5) ∧ (p1 ∧ p1))) ∨ p2)) → (p1 ∨ True)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200820676813710172281940773304 : ((p5 ∧ (p3 ∧ ((p4 → False) → (True → False)))) → (((p1 → (p2 → (p1 ∨ True))) → (p2 ∨ ((p1 → p2) ∨ True))) ∨ ((p1 ∨ True) → p2))) := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173053439682760693572951913253 : ((False ∨ ((p4 → (((True ∨ ((p3 ∧ False) → p3)) → p2) → (True ∨ p2))) → p4)) ∨ (False → (False ∧ (p2 → ((p3 → p3) → (False ∧ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341071120292119199463422620864 : (p2 → ((p5 ∨ ((((((True ∧ p2) → (p2 → (True ∧ False))) ∨ (p4 ∨ True)) ∧ p2) ∧ False) ∧ (((p4 ∧ (p5 ∧ False)) ∧ p2) ∨ p4))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779532826002855683063719970577 : (((p2 ∨ (((p3 → (p4 ∨ p2)) → (p2 → (False ∧ ((p3 ∧ ((p4 ∧ ((p2 → ((False → False) → p5)) ∧ False)) ∨ False)) ∨ p3)))) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_187737660964879689031784115378 : ((p1 → (False ∨ ((True → ((p3 ∧ True) ∧ p3)) → (True ∨ p4)))) → ((((p2 ∧ True) ∧ ((True ∨ p2) ∨ True)) → (p5 → (p4 ∨ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231535571809628895310305978797 : (((p4 → p4) ∨ p2) → ((((p3 ∨ (p2 → ((False ∧ p5) → False))) ∨ (((p5 ∨ p5) → p2) → p2)) ∨ p3) ∧ ((p2 → (p2 → p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h12 =>
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
theorem thm_5_vars_349090711692256435502466187392 : (p3 → (True → ((((p1 → ((((False ∨ p5) ∨ (p1 ∧ False)) ∧ p2) ∨ ((((p4 ∨ False) → p2) → (p2 → False)) ∧ p2))) → p1) ∨ p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115457658306320567062824590354 : ((((p2 ∧ p1) → (p4 ∨ ((p3 ∨ p2) → False))) ∨ (p2 → ((p3 ∨ ((p3 → (False ∧ (False ∨ (p3 → p3)))) → p4)) ∨ p5))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614547274270290273868024615777 : (((((((True ∨ (p4 → p3)) ∧ (p5 ∧ p4)) ∧ (((p4 → (p1 ∨ (False → False))) ∧ p3) ∧ p1)) ∧ ((p1 ∨ (False ∧ p4)) ∧ p4)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_320293124796122426975253049939 : (p4 ∨ ((p4 ∧ p5) ∨ (((p1 ∨ (p5 → False)) ∨ (True → p5)) ∨ ((p3 ∨ p5) ∨ ((False ∧ (p3 → (p5 ∨ (p4 ∧ p4)))) → (p1 ∧ p3)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137183649912956816633127964335 : ((False ∧ ((p5 ∨ ((p3 ∨ (p2 ∨ p1)) ∨ p5)) → ((((p2 ∨ (p3 ∨ (p5 ∨ p5))) ∨ False) → p5) ∨ (False ∧ p1)))) ∨ ((False ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80338342170016739047644446676 : ((((False ∨ ((((p1 → ((p2 → False) → p4)) → (p1 → p3)) → (p4 → p2)) ∧ True)) ∨ (p4 ∨ ((p2 ∨ True) ∧ True))) → (p3 ∧ p4)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∨ ((((p1 → ((p2 → False) → p4)) → (p1 → p3)) → (p4 → p2)) ∧ True)) ∨ (p4 ∨ ((p2 ∨ True) ∧ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616399540260991309717672709834 : (((((((p1 ∧ ((p1 ∧ (p4 ∧ (p2 ∨ True))) ∨ False)) ∧ p3) ∨ True) → ((((p5 ∧ False) ∧ p1) ∧ (True → p3)) ∨ (False → p4))) ∨ p4) ∨ p2) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- False on the left can always be used.
    apply False.elim h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259083027642173235829357454431 : ((True → p5) → (((((p4 ∨ p4) ∧ p1) ∧ ((((p1 ∨ False) ∧ p5) ∨ (False ∧ (p4 → p4))) → p1)) ∨ (p2 ∨ p4)) ∨ (True → (p4 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211673213765781776381246732581 : (((p5 → p2) → (True ∨ p2)) ∧ (((((p2 → (p1 ∨ False)) ∨ p3) → (((False ∨ p2) ∨ (p5 ∧ True)) ∧ (p1 ∧ p5))) ∧ (p3 ∧ p5)) → p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : ((p2 → (p1 ∨ False)) ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44336647206214485523047709559 : (((((((True → p1) ∨ False) → ((((p4 ∧ (False → p5)) ∨ p5) → p2) → p5)) → p2) → (((True ∧ p2) ∧ (True ∨ False)) → p2)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225677312882386275909062958710 : (((p2 → p5) ∧ p3) ∨ ((p2 → p3) ∨ ((p2 ∨ (((p4 ∨ p5) ∨ p1) ∨ (p4 → ((p5 ∧ True) ∨ True)))) ∨ ((p5 ∧ (p5 ∨ p3)) ∨ p4)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317813118294252769571873063133 : (p4 ∨ (((((False ∨ p3) ∨ p3) ∨ (True ∧ p4)) → ((((p5 ∨ p2) → (True ∧ ((p5 ∧ p4) → p5))) ∧ p5) ∧ ((False → False) → p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126047789761812169277387702193 : (((p3 → p5) → ((p2 → (((p1 ∨ (p1 ∨ False)) ∧ p4) ∨ p1)) → ((p4 → False) ∧ ((p1 ∨ (False → (p3 ∨ p5))) ∨ p1)))) → (p5 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196591411974068808187043084099 : ((p4 → ((p1 ∨ True) ∨ (p3 → (p2 ∨ p1)))) ∧ ((((True → ((False ∨ p2) → p2)) → p1) ∧ (((True ∧ p4) → p5) ∧ p5)) ∨ (False → False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623452203432798090657872196288 : ((((False ∨ (((True ∨ (p5 ∨ (p1 ∨ False))) → (p2 → (((p1 → (p5 → p1)) → False) ∧ (p5 ∧ (p3 → False))))) ∨ (False → p2))) ∨ p2) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314539229016789896336098871572 : (p3 ∨ ((((p4 ∨ (((((p1 ∧ p1) ∧ (False ∨ p4)) → True) ∨ p3) ∨ True)) → (p4 → p3)) → p4) ∨ ((p4 ∧ ((p3 → p1) ∧ p1)) → p1))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114436948887818817895559076162 : (((p3 ∨ (((p4 → p5) ∧ (p2 → ((p3 ∨ (p1 → p4)) ∨ False))) ∧ (p1 ∧ (True ∧ True)))) ∨ (((p1 ∧ False) ∧ p2) ∨ p5)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204321259266292442292529635486 : (((p2 ∧ (p3 ∨ (p4 ∧ p1))) ∧ True) ∨ (((p1 ∨ True) ∨ (p3 → (p5 ∧ True))) ∨ (p3 ∧ ((p5 → ((False ∨ p3) → False)) ∧ (p3 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593935959202881257133648761207 : ((((((p5 ∧ (False ∨ (p2 → (p3 → p2)))) ∧ (((p2 ∧ (True ∧ p3)) ∨ False) ∧ (p1 ∧ p1))) ∨ (((p4 → p3) ∨ p4) ∧ p4)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81238177654993395441406518115 : (((True → (False ∧ (((False → ((p4 → True) → p1)) → p2) ∧ ((((p3 → p2) ∧ p2) ∨ False) ∨ (p1 → p5))))) ∧ (p1 ∨ (p5 → True))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111898071628697473996400425645 : ((((p1 → (((((p4 ∧ False) ∨ (True ∧ (p4 → p2))) ∨ p5) → p3) → False)) ∨ (p3 ∨ (((False ∨ p2) ∧ p4) ∨ p5))) ∨ p1) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191867454392470392673719287485 : ((p4 ∨ ((p1 ∧ (p5 ∧ (p3 → p4))) ∧ (p2 → p3))) ∨ ((((True ∧ p2) → (((p1 → p3) ∧ p5) → True)) ∧ (False → p3)) ∨ (True ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50393113019771810344103749478 : ((((p5 → p2) ∨ (p3 → (((((p2 ∧ p1) → (p1 → (p3 ∨ True))) ∧ p3) ∨ (False → False)) → p2))) ∨ (((p1 ∧ p3) → False) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633921055507425912930316232081 : (((((((((p1 ∧ p5) ∨ (p2 ∧ p2)) ∨ (((((p4 ∧ p4) → p5) ∨ p4) → False) → (p5 ∨ True))) ∨ False) → p3) → (True ∨ False)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50475648987327708944076405275 : (((p1 → (((p4 ∧ (False ∨ (True ∨ p2))) ∧ (p1 ∧ True)) ∨ (((False → (True → p3)) ∧ False) ∧ True))) ∨ (p5 → (p1 ∧ (False ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314417006828172138875809371556 : (p3 ∨ (((p3 → (p2 ∨ (p3 ∧ (True ∨ (((p4 → p3) ∨ True) ∨ (p1 ∨ (True → p5))))))) → (p5 ∧ p2)) ∨ ((p3 ∧ False) → (p1 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300666415096970208140014968353 : (False ∨ ((((((False ∨ (p5 ∨ (p1 ∧ True))) ∧ ((True → p1) ∧ True)) → True) → (p1 ∧ p1)) ∨ p1) ∨ ((p3 → p3) ∨ ((p2 ∨ p5) → True)))) := by
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
theorem thm_5_vars_629831128023085108920262558795 : ((((((((((p5 ∧ False) ∨ p3) ∨ (p4 ∨ p2)) ∧ False) ∧ p3) ∨ (((p2 ∨ p3) ∧ False) → ((p3 → (False ∧ p5)) ∧ p3))) ∨ p1) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



