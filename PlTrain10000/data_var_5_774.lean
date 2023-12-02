variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809023795500251008158217826523 : (((p5 → (((p3 ∧ False) ∨ ((False ∨ ((p4 → ((((p5 → True) → (False ∨ (p3 → True))) ∧ p5) ∧ p3)) → p2)) → (p2 ∨ p5))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328681426638222003508222859684 : (True → (((p3 ∧ p1) → (((p4 ∨ ((True ∨ p1) → p1)) ∧ False) ∨ True)) ∧ (p1 ∨ ((p3 ∨ (p1 ∨ (p2 → True))) ∨ ((p2 ∨ p4) ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147989491525382694324075136598 : (((((p2 ∧ (True → (p1 ∧ p5))) → (p4 ∨ (p4 ∧ ((p1 → (p1 ∨ p3)) → p1)))) ∨ p2) ∨ (p1 ∧ p4)) ∨ (True → ((p3 → True) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187019286676010182749159489921 : (((False ∨ (p4 ∧ True)) → ((p3 ∧ (True ∨ (p2 ∨ p1))) ∧ p1)) → ((True → (p2 ∧ (p2 ∨ p4))) → ((p1 → p3) → ((p2 → False) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184908301469168384630358693261 : ((((p5 ∨ p5) ∨ p1) ∨ (((False → (p5 ∧ p3)) ∨ False) ∧ p3)) ∨ ((p4 ∧ (p4 ∨ False)) → ((False ∧ p1) ∨ (((p4 ∧ p3) → p2) ∨ p4)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346814620788149644352915779555 : (p3 → (((((p3 ∧ ((p2 ∨ p5) ∨ True)) ∨ p2) ∨ ((False → ((False ∨ True) → p5)) ∨ (p5 ∨ True))) ∨ p1) → ((p1 ∨ True) ∨ (p4 ∨ True)))) := by
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
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
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
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h17 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h18 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588000556533845369248308628458 : ((((((((p2 ∨ ((p5 → p2) ∨ (p1 → (True ∨ p4)))) ∧ (p1 → p1)) ∨ (p1 ∧ p5)) ∧ (p2 ∧ (True ∧ (p2 ∧ p3)))) ∨ p1) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193050261221609093419535654198 : (((False → (p3 → ((True ∧ p4) → p3))) → (p2 ∧ p3)) → ((p2 ∧ p5) → (((p2 → p4) ∧ ((p3 ∨ (True → p5)) ∧ p5)) ∨ (p1 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (False → (p3 → ((True ∧ p4) → p3))) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h5
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217265992304634545565050411290 : (((p1 ∧ (p4 → p2)) ∨ p4) → ((p2 ∨ ((p3 → ((p3 → p4) ∨ (False → p2))) ∧ p5)) → (p2 ∨ ((((p3 ∨ p2) ∧ p1) ∨ p4) ∨ True)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
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
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641270786434575051167997148229 : (((((True → True) ∨ (((True → ((((p1 ∧ p1) ∧ p3) ∨ ((p1 → True) ∨ ((p1 ∨ p5) ∨ p3))) ∧ True)) ∨ p3) → (True ∨ p3))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50795570133322705434587034051 : (((True → (p4 ∨ ((False ∨ (False ∨ (False ∨ (False → ((p5 ∨ p3) → ((p2 ∨ p5) ∨ p4)))))) → p1))) → (((p2 → p2) → p2) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264315979297506885683764684498 : (True ∧ ((p3 ∧ ((p3 ∨ (p5 ∨ p1)) → p1)) → (p1 ∨ (p2 ∧ (p5 ∨ ((True ∨ (((p2 → False) → (p1 ∧ p5)) ∨ p1)) ∧ (p4 ∨ True))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p3 ∨ (p5 ∨ p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317852608421394694425395246419 : (p4 ∨ (((p2 ∨ False) ∧ ((((((False → p1) ∧ p4) → ((True → (p4 ∨ True)) → p1)) ∨ ((p1 ∧ p5) ∧ p3)) ∨ p2) ∨ (p2 ∧ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152130701398793092206972783616 : (((p2 ∧ ((p4 ∨ (p1 ∧ p3)) → (p5 ∨ p1))) ∧ (p3 ∨ (p2 → ((p4 → False) ∨ ((p1 ∧ True) → p1))))) → ((p2 ∧ (True → False)) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711743573877271914061552874139 : (((((((p4 ∧ p4) ∧ p1) ∨ p1) ∧ p3) ∨ ((((p4 → p5) ∨ p1) ∨ False) → (((True → ((True ∨ p4) → (p3 ∧ p4))) ∧ p5) → p4))) ∨ p2) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h8 := h3 h7
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : (True ∨ p4) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h10 := h8 h9
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h14 := h3 h13
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h15 : (True ∨ p4) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h16 := h14 h15
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h18 =>
    -- False on the left can always be used.
    apply False.elim h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68293433166737884694126972112 : ((p3 → (((p1 ∧ p1) ∨ ((p2 ∨ ((p3 ∨ p3) → (((False → True) ∧ (p2 ∨ True)) ∨ p3))) → (p4 ∨ p2))) ∨ ((p5 → p5) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694263392190913286091951380031 : (((((True → (p5 → (p5 → p1))) → (p1 → (((p1 ∧ p5) → False) ∨ p5))) ∨ (p4 → ((((p2 → p5) ∧ (False → p2)) → p4) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777761336372034251957463550660 : (((p1 ∨ (((p1 ∨ p4) ∧ (False ∧ (p4 → p2))) ∨ (p3 ∨ ((False ∨ (p5 ∨ (p4 → p5))) → (((p3 → (p4 ∨ p5)) ∨ p3) ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56257648932700129497455325293 : (((p1 → (False ∨ (p3 ∧ p3))) ∨ ((p2 ∧ (True → (((p2 ∧ (p5 ∨ p5)) ∧ p5) ∨ (p5 ∧ ((p5 → (p5 ∧ p5)) ∨ p5))))) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790978107178925090226600987174 : (((p5 ∨ (p5 → (p1 ∨ (False ∨ ((p5 ∧ ((p1 ∨ p5) → (p5 ∨ p2))) → ((p2 → ((((p2 → p2) → True) → True) → p1)) ∨ True)))))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_324222711850145779443522397820 : (p5 ∨ (((p1 ∧ ((False ∨ (p4 → p1)) ∧ p2)) ∨ True) ∧ ((p1 ∧ p1) ∨ ((p5 ∨ (((p5 → p4) → (True → p3)) ∧ True)) → (False → p3))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47209422915599688986057839513 : ((((p1 → ((p1 → p2) ∨ ((p1 ∨ p1) → (p5 → False)))) ∧ (p3 ∧ ((p3 → (((p3 ∧ p1) ∧ p2) ∧ True)) → False))) ∨ (p3 → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148655012130730790954402216643 : ((((p2 ∧ True) ∨ (p5 ∧ ((p1 ∨ p3) ∧ p4))) ∧ ((p3 ∨ ((p2 → True) ∨ ((False ∨ p4) ∨ p3))) ∨ p4)) ∨ (p2 ∨ ((p5 ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51017728908443299678430941774 : (((p1 ∧ ((p3 ∧ ((p5 → (True ∨ p5)) ∧ p2)) ∨ (((p5 ∧ (p1 → p4)) → p2) → p5))) ∧ ((p5 ∧ False) ∧ ((p5 ∧ p1) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779275563006381937996212845349 : (((p2 ∨ (((p2 ∨ True) → (False ∧ ((((((p2 ∧ p3) ∧ p5) ∨ (((p3 ∨ p3) → p5) ∧ p1)) ∨ True) ∧ False) ∨ (p3 ∧ p1)))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140212523618887246193032310433 : ((((p1 → p1) → ((True ∧ (p5 ∧ p3)) ∧ ((p2 ∧ (p2 ∨ p5)) ∨ (p4 ∧ (p4 ∨ (p5 → False)))))) → (False ∧ p4)) → (p3 → (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208861017751383361457555279363 : ((p4 ∧ (((p2 ∧ p1) ∧ p3) → p4)) → ((((((p2 ∨ False) ∨ p3) ∧ True) ∨ (((p4 → p1) → p5) ∧ (True → (p4 ∨ p3)))) ∨ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805125791811405722459363558451 : (((p3 → (p1 ∧ ((p4 → (((p5 ∧ p3) → (((p5 ∨ p2) → (p1 → (p1 ∨ p1))) → (p4 ∧ ((False ∨ True) ∨ p3)))) ∧ p2)) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56748097699814990441075141633 : ((((p1 → False) ∨ False) ∧ (p5 ∧ ((False → p2) ∧ ((p2 ∨ (False ∧ p3)) ∧ ((True ∨ (p3 ∨ p3)) ∨ (((p4 → p4) ∧ p4) ∧ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49120198350304998471295868968 : ((((p1 ∧ (((True ∧ (((p2 → (p4 ∧ False)) ∨ p4) ∨ False)) ∨ False) → p1)) → (((p3 ∨ True) → p2) ∧ p4)) ∨ ((True ∨ False) ∨ p5)) ∨ False) := by
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
theorem thm_5_vars_179897551707467165904239112720 : ((((p4 → ((True ∨ ((p5 ∨ False) → (p5 ∧ p5))) ∨ p5)) ∧ True) ∨ False) → ((((((p4 → p1) → p5) → p3) ∧ p5) ∧ p2) → (p3 ∧ p3))) := by
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
  cases h1
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h10 : ((p4 → p1) → p5) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h12 := h5 h10
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h2.left
  let h15 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h21 : ((p4 → p1) → p5) := by
      -- Implications on the right can always be decomposed.
      intro h22
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h23 := h16 h21
    -- One of the premise coincides with the conclusion.
    exact h23
  case inr h24 =>
    -- False on the left can always be used.
    apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344775554745058059126637434978 : (p2 → (p4 → ((p3 ∨ ((p1 ∧ ((True ∨ (p1 → False)) → (p1 ∨ True))) ∨ ((((p4 ∨ p2) → p5) ∧ (True ∨ (p1 ∧ p2))) → False))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247794323919230143405855968239 : ((p1 ∨ p1) ∨ (((p2 ∧ p5) → ((True ∨ p2) ∧ ((p5 ∨ (True → p3)) ∧ p1))) ∨ ((p3 → (p3 ∧ p5)) → (p3 → ((p4 → p2) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313974674930515265999553738859 : (p3 ∨ (((((((True → p5) ∧ p3) ∨ True) → (p4 ∨ True)) → (p5 ∨ p2)) ∨ (p5 ∨ ((((p2 ∧ p3) → p5) ∨ p2) → p2))) ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190516054070221141240206415719 : (((((p3 ∨ (False → (p2 ∨ False))) ∨ p1) → p2) → p3) ∨ (((p5 ∧ (p5 → p2)) ∨ ((p3 ∧ (True ∧ False)) → p1)) ∧ (p3 ∨ (False ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148170933400435967556741879841 : (((((p2 ∨ p5) ∧ (p2 ∧ ((p3 ∨ p4) ∧ (True → ((True ∧ False) ∧ p5))))) ∨ p5) ∧ ((p1 ∧ p2) ∨ False)) ∨ ((p4 → (p1 ∧ p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60318152974338919713296533297 : (((p1 → p5) → (((((False → p1) ∨ p2) ∨ (p4 → (((p4 ∧ p3) → ((p4 ∧ p3) ∧ p1)) ∧ (p3 → p5)))) → (p1 → p5)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38503340572513822048539711712 : (((((p3 → (p2 → p5)) ∧ ((p5 ∧ (p4 ∨ (True ∨ p3))) → p5)) ∨ (((True ∧ False) ∨ p3) ∨ (False ∧ ((p2 → p5) ∧ p2)))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48584164371289463176907967768 : (((((((p5 ∧ (((p1 → (p2 → p5)) → p3) → p4)) ∧ (p3 ∧ p5)) ∧ (p5 ∨ p4)) ∧ p4) ∧ (p2 ∧ p3)) ∧ (p2 ∧ (p4 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344296305565543382423751426078 : (p2 → (p3 ∨ ((((p4 → p5) → ((((p1 ∨ (False ∧ (True → p5))) ∧ p4) ∧ p5) ∨ ((p3 → p1) ∨ (p3 → p1)))) ∨ p2) ∧ (True → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39036095745309187712427990666 : ((((p4 → p4) ∧ ((p5 ∧ (((p3 → p4) → p3) ∧ (p2 ∨ (((p5 → (p4 → (True ∧ (p5 ∨ p3)))) → False) → p3)))) ∧ p1)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113645742398036526723251987649 : ((((((p2 ∧ p5) ∧ ((p1 ∧ (((False ∧ p3) → p5) ∧ p5)) ∨ (False → (p1 ∨ True)))) ∨ (p3 ∨ True)) ∧ p2) → (True ∧ p1)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140587792282389591856890961130 : ((((p4 ∨ (((p5 ∨ ((p5 ∨ p5) ∧ True)) → ((True ∧ False) ∧ p1)) → p2)) ∧ False) → ((p1 → p4) ∧ (p2 ∨ p4))) → ((p5 → p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720828903255685999995957626939 : (((((False → (p4 ∧ p5)) → p3) → (p3 → (((((True ∧ (p1 ∨ (p4 → p2))) → p1) ∧ False) → False) → ((False ∧ (p2 ∨ p4)) ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254149171115789121422140944926 : ((p2 ∧ p1) → (((((p1 → p1) ∧ ((((p2 → True) ∨ (False ∧ (False → p1))) → p5) ∨ p2)) ∧ True) → (((p2 → p2) → False) ∨ p1)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204492890786713050517108319512 : (((((p2 → p4) → False) ∨ p5) ∨ False) ∨ (((True → (False ∧ p2)) ∨ (((p5 ∨ (p2 ∨ p4)) ∨ (p5 ∧ (p5 ∧ p1))) → True)) ∨ (p2 ∨ p4))) := by
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
theorem thm_5_vars_135987383519981861414089379978 : (((((p4 ∨ p1) → (p2 ∨ p2)) ∧ ((p3 ∨ True) ∨ p4)) ∨ (False → ((p2 → ((p2 ∨ p4) ∧ (p5 → False))) → False))) ∨ (p1 → (p5 ∧ False))) := by
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
theorem thm_5_vars_187253465087485481278034106428 : ((True ∧ ((False → False) → ((False → ((p3 ∨ p1) ∧ True)) ∧ p3))) → (((p5 ∧ p2) ∨ ((p3 ∧ p4) → (p5 → False))) ∨ ((False → p3) → True))) := by
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
theorem thm_5_vars_58964121718767858381471547768 : (((p2 ∧ p2) ∨ (((p2 ∧ p5) ∨ ((((False ∧ False) → (p1 ∨ p4)) → (p5 ∧ (p2 ∧ p3))) ∨ p2)) ∨ (False → (p3 ∧ (p3 → p1))))) ∨ False) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49162833442043296732195749296 : ((((p3 ∧ ((p1 ∧ (p4 ∧ True)) ∧ p5)) ∧ ((True → p1) ∨ ((p4 ∨ p1) ∨ (p4 → (p1 → (False → p5)))))) ∨ ((False ∧ p2) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60552019139250608417806954147 : ((True ∧ ((False ∨ ((((p1 → p4) ∧ p5) → (p5 ∨ ((p5 ∧ (p3 ∧ p2)) → (p5 ∧ (True ∨ (True ∨ (p4 ∧ p1))))))) → p1)) ∨ True)) ∨ p5) := by
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
theorem thm_5_vars_55126859865866983990911819760 : ((((False ∧ (p4 ∨ (p5 → True))) ∧ p1) ∨ (False ∨ ((True ∧ (((p2 → p1) → p3) ∨ p5)) → (((True ∨ (True ∨ p5)) ∧ p1) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336162453190138263087399719462 : (p1 → ((((False → ((False ∨ (p2 → p4)) ∨ ((p3 ∨ ((p5 ∧ p1) ∨ True)) ∨ False))) → ((True ∨ (p5 ∧ (p3 → p1))) ∨ p5)) → p2) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607015073854476408449838745354 : (((((((((p4 ∧ True) → (p3 → (p1 ∨ False))) ∨ False) ∧ (p2 ∨ p1)) ∧ ((p5 ∧ p5) → (((p4 ∧ False) ∨ p5) → True))) ∧ p5) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55202245009687713564115141772 : (((((p2 → False) ∧ p3) ∧ (p2 → False)) ∨ (((((True ∨ p1) ∧ (True ∨ ((p4 ∧ True) ∨ p2))) → p2) ∧ p1) ∨ (p4 ∨ (True ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613009372253439891392527013527 : ((((((((p3 → (p2 ∨ False)) ∧ p3) ∧ (((False ∧ ((p3 ∨ True) ∧ p2)) ∧ False) → ((p1 ∨ p1) ∧ False))) ∧ p5) → (True → p4)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_48083768267777858710961071422 : ((((p1 → (p5 → (p4 → (True ∨ p2)))) ∨ (p2 ∨ (((((p3 → p4) ∨ ((p3 ∧ p3) → True)) → False) ∨ p4) ∨ p4))) → (p4 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56149789491517944299913392585 : ((((p2 → p1) → (True ∧ False)) ∨ (((p2 → p4) ∨ p5) ∨ (True → (p2 ∨ (True ∧ ((p1 ∨ (p1 ∨ p2)) ∧ ((True → p1) ∨ p5))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179563421963562614269659301914 : ((p2 → ((True ∧ (p3 → (((p5 → (p5 ∧ p3)) → p3) ∧ p2))) → p5)) ∨ (((p4 → ((p1 ∧ p3) → (False → (p2 ∧ p1)))) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41402959550283154664141948787 : (((((((((p2 ∧ True) ∧ p2) → p5) → p2) ∨ (p1 → (True ∧ True))) ∧ p3) ∨ ((p2 ∨ False) ∧ (p4 → (p2 → (True ∨ p3))))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137014487722799769702747144819 : (((p2 ∨ p1) → (((True ∧ (p2 ∨ ((p2 ∧ (True ∨ (p2 ∨ p3))) ∧ p2))) ∧ (True → p4)) → (p2 ∧ (p1 ∨ False)))) ∨ ((False ∧ p5) → p3)) := by
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
theorem thm_5_vars_248023836493000130255542731453 : ((p1 ∨ p5) ∨ ((True → ((p5 ∧ ((False ∧ p5) → p3)) ∧ (((p5 ∧ (p1 → (((False ∨ (p3 ∧ False)) ∧ p2) ∧ p5))) ∧ p4) ∨ p4))) → p4)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759476662046391087645798162008 : (((p2 ∧ (((p5 → ((p3 ∧ ((p5 → ((p4 → (p1 ∧ False)) ∧ p4)) ∨ p5)) ∧ (False ∨ p1))) ∨ False) ∨ ((p3 → False) ∨ (p2 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_240015004424149751207082378249 : ((p4 ∨ True) ∧ (((((True ∧ False) → True) → p3) ∨ (False → (((p3 → p1) → False) ∨ (p5 → ((True → True) ∧ p2))))) → ((p2 ∧ p3) → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54992065293620341631676833517 : ((((p4 ∧ p3) ∨ ((p1 ∨ p3) ∨ True)) ∧ ((((((p2 → p4) ∨ p1) ∧ p3) ∨ p5) ∨ ((p2 → p4) ∨ (True → (p3 → p4)))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114987983040834445205091660001 : ((((p1 ∧ (((((p4 → p4) → p1) → p4) ∨ p5) ∧ True)) → p5) ∧ (((((p4 ∨ p3) ∧ p3) ∨ True) ∧ (p3 ∨ p1)) ∧ p2)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160791151245635210662039273414 : (((((p5 → p2) → (True ∧ False)) → True) ∨ (p1 ∨ ((p3 ∨ ((p2 ∨ p2) → p4)) ∨ (p3 ∧ p1)))) → ((False ∨ (p1 → (p4 → p4))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- Implications on the right can always be decomposed.
          intro h13
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h15
          -- Implications on the right can always be decomposed.
          intro h16
          -- One of the premise coincides with the conclusion.
          exact h16
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- Implications on the right can always be decomposed.
        intro h21
        -- One of the premise coincides with the conclusion.
        exact h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324167754682036825237800653806 : (p5 ∨ (((((p5 → p2) ∨ p3) → (p2 → p4)) ∨ (True → p3)) ∨ (((False ∧ p3) ∧ (True → ((p2 ∧ (p2 → (p4 ∨ p3))) ∧ True))) → p1))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112193677560885463789544102530 : (((p5 ∧ (p5 ∨ (p5 ∧ (((p2 ∨ (False → p4)) ∧ ((p2 ∨ (False → (p3 ∨ p1))) ∨ p1)) ∧ ((p2 ∨ False) ∨ p4))))) ∨ p2) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352840647942944022042943113569 : (p4 → ((p3 → True) → ((p5 → ((p3 ∨ False) ∧ (p1 ∨ (((True → p2) ∨ p1) → (((p1 → p2) → p3) → (p5 ∨ False)))))) ∨ (p2 ∨ True)))) := by
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
theorem thm_5_vars_227053121331619697970579197995 : (((p2 ∨ p5) → p1) ∨ (((p3 ∧ ((True → ((False ∧ ((p3 → p5) ∧ p3)) ∨ (p4 ∨ True))) ∧ False)) ∨ (p3 → p3)) ∨ (p3 ∨ (True ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340836940268291455645523454252 : (p2 → (((p1 ∧ ((((True ∨ p5) → ((p4 ∧ p2) → p2)) ∧ (p2 ∧ p5)) ∨ ((False ∨ (p5 ∨ p3)) ∧ (p5 → p1)))) → (p3 ∧ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111635453956244237116357041694 : (((((((p1 → (p2 ∨ (((p5 ∨ True) ∨ True) ∧ p1))) ∧ p3) ∨ p2) → ((True ∧ (p1 ∨ p4)) ∨ (p3 ∨ p3))) ∨ p5) ∨ True) ∨ (p5 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323521767037056069980132171166 : (p5 ∨ ((False ∨ ((((((p2 → ((p2 ∨ p2) ∨ (p3 ∨ False))) ∧ p5) → p1) → (p1 ∧ True)) ∨ p2) ∧ (p2 ∧ p2))) ∨ ((p5 ∨ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121711332295730112376122952772 : ((((False ∨ ((p2 ∧ (p3 ∧ False)) ∨ (True ∨ p1))) ∨ ((((True ∧ (False ∧ (p3 ∧ p4))) ∨ p5) → (True ∧ p4)) ∧ p4)) → False) → (False ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∨ ((p2 ∧ (p3 ∧ False)) ∨ (True ∨ p1))) ∨ ((((True ∧ (False ∧ (p3 ∧ p4))) ∨ p5) → (True ∧ p4)) ∧ p4)) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321134088916244249357343502776 : (p4 ∨ (p2 ∨ (((p3 ∧ (p3 ∧ (((p3 ∧ p3) ∧ p1) ∧ p1))) ∨ p5) ∨ ((False ∧ (p1 → (p1 ∨ p3))) → (False → (p4 → (p4 ∧ p2))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114624284077211756804005622531 : ((((p4 ∧ (((p2 ∧ p2) ∨ (p1 → p1)) → ((p5 → (False → False)) ∨ True))) ∧ p2) ∨ (p4 ∧ ((True ∧ (p5 ∧ p2)) ∧ p4))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160984895090181925712526977295 : ((((True ∧ p4) ∧ p3) ∨ (((True → ((p2 ∨ p4) ∧ ((p5 ∧ p4) ∨ False))) ∧ (p4 → p1)) → p1)) → ((p3 → (p3 → p2)) ∨ (False ∨ True))) := by
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
theorem thm_5_vars_223346888523600577628165184222 : ((True ∨ (p4 ∧ False)) ∧ ((p5 ∧ (True ∨ True)) → (((((p2 ∨ (p4 ∧ ((True ∧ p4) → False))) ∨ True) ∨ ((p2 → p4) → p2)) → False) → p2))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : (((p2 ∨ (p4 ∧ ((True ∧ p4) → False))) ∨ True) ∨ ((p2 → p4) → p2)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : (((p2 ∨ (p4 ∧ ((True ∧ p4) → False))) ∨ True) ∨ ((p2 → p4) → p2)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133678625470250984751729992996 : ((((((p5 ∨ p4) ∨ ((((p5 ∧ p5) → p5) ∨ p5) ∧ ((p3 ∧ p3) → p4))) ∧ p2) ∧ (p1 ∧ (p4 → p1))) ∧ p4) ∨ (p5 → (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707259052529870779236533077479 : ((((((True → p1) ∧ (p3 ∨ p1)) ∧ (p4 ∨ p3)) ∨ (True ∧ (False ∧ (((((((True → True) ∨ p5) → True) ∧ p3) → True) → False) ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105116483375787699908579970034 : (((((False ∧ (p3 ∨ (p3 ∧ False))) ∨ ((p4 → (p2 ∨ (p3 → (False ∨ p3)))) ∧ p2)) ∨ (p3 ∨ True)) ∨ ((p3 → False) ∨ p2)) ∧ (False → p5)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597655762553722545836977078629 : ((((((p3 ∨ (p2 ∨ False)) → True) → (p2 → ((p2 ∧ p1) → ((True ∨ ((p5 ∧ p1) ∧ (True ∧ (p4 ∨ p1)))) → (False ∨ False))))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784137561977933798706350897422 : (((p3 ∨ ((p1 ∧ p1) → (p2 ∨ (p3 ∨ (p3 → (((p5 → p1) → ((((p2 ∧ p1) → True) ∨ p4) → False)) ∨ ((False → p2) ∨ p2))))))) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748569244649904731841362074206 : ((((p3 → False) → (p1 ∨ ((((p4 → p3) → ((p5 ∨ ((p1 ∨ (p2 → p2)) ∧ True)) ∨ (((p4 ∧ p2) ∧ True) ∧ False))) → False) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213588468701267314789124729123 : ((((False → p4) ∧ p1) ∨ p4) ∨ ((((p4 ∧ p3) ∧ (((False ∨ p2) → True) ∨ p3)) → (False ∨ (p5 ∨ (p2 → ((p1 → False) ∨ p4))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37856391184576009467175518268 : ((((p1 → (((p4 ∨ p5) ∨ p1) ∨ (p2 ∨ (p3 ∨ ((p1 ∨ (((False ∨ (True ∨ p4)) → True) ∨ False)) ∨ (p5 ∧ p4)))))) → p4) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147475395570924826845931931538 : (((p2 ∧ (((((p4 → False) → p4) ∧ ((p3 ∨ p5) → (((False ∨ p2) ∨ p2) ∨ p2))) → p1) ∨ True)) ∨ True) ∨ ((p2 ∧ (p4 ∧ True)) ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330723840641228346904186718867 : (True → (p1 → ((p5 ∧ ((((p1 ∧ (p5 → p5)) ∨ (p1 ∧ True)) ∨ ((p2 ∨ ((p1 ∨ p5) ∧ p3)) → p2)) → ((p4 ∧ p3) ∨ p1))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179991061886696953207001310789 : (((((p2 ∨ p5) ∨ p3) ∨ ((((p4 ∧ p2) ∧ p5) → p1) ∧ p3)) ∨ True) → (True → (((False ∨ True) ∧ (False → (p3 ∨ (p5 → p1)))) ∨ p3))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
          -- Implications on the right can always be decomposed.
          intro h7
          -- False on the left can always be used.
          apply False.elim h7
        case inr h8 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
          -- Implications on the right can always be decomposed.
          intro h9
          -- False on the left can always be used.
          apply False.elim h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h15
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340788465992836136780231471118 : (p2 → ((((((p5 ∨ False) ∨ (False ∨ True)) → p1) ∧ ((p2 ∨ p2) → ((p2 ∨ ((p4 ∨ (p2 ∨ True)) ∧ (p3 ∧ p4))) → p1))) → p5) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119219745292085790496520191255 : ((p2 → ((p3 → ((p2 ∧ p3) ∧ False)) ∨ ((True → (False ∨ p4)) → ((p1 ∧ (p2 ∧ False)) ∨ (((p5 ∨ False) ∨ True) ∨ p1))))) ∨ (p4 ∨ p5)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147690505774221138722290470087 : ((((p1 ∨ (False ∨ (p1 ∧ (((p5 ∨ True) ∧ (p4 ∨ p1)) ∧ (p5 ∧ p4))))) → (p2 ∧ (p4 ∨ p5))) → p2) ∨ (((False → p4) ∧ False) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313020726919405133177761393615 : (p3 ∨ (((p4 ∧ ((False → (((((p2 ∧ p5) ∧ (False → p2)) ∧ p4) → ((p3 ∨ (False → True)) ∧ (p4 ∧ True))) ∧ p4)) → p4)) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161847843055182970193810269838 : ((True → ((p4 ∧ p1) ∧ ((p4 → ((p4 ∧ p1) ∨ p4)) ∧ (p2 ∨ ((p5 ∧ p1) ∧ (False ∧ p1)))))) → ((p4 ∧ ((p2 ∨ True) ∧ p5)) → p2)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h16.left
      let h20 := h16.right
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799954548364335204040330424329 : (((p2 → ((((p1 → False) ∨ (p3 ∧ (((p5 ∧ True) ∧ p5) ∨ (((False ∧ p3) ∧ (((p1 ∨ True) → True) ∧ p2)) → False)))) ∨ p4) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718766076637809103999757446407 : (((((p3 ∧ p2) ∨ (p1 ∧ p4)) ∨ (p5 → ((((False ∧ p4) ∨ ((True ∧ ((p4 → p2) → ((p4 ∨ p4) ∨ False))) ∧ p5)) ∨ p5) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678665443427026638902365235231 : (((((p2 ∧ p5) ∨ (p5 ∨ (False ∨ (((p3 → (p4 → (p3 ∧ (p5 → p4)))) ∨ (p4 ∧ False)) ∧ p1)))) ∨ ((p3 → (p3 ∧ True)) ∨ p5)) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60178097155622037163513845666 : (((p5 ∨ p1) → ((((False → (((False ∨ False) → ((p4 ∨ p4) → p3)) ∧ (p1 ∨ p5))) ∨ (p3 ∧ (p2 → p2))) → p5) ∨ (p5 → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205186337940380826884258237580 : (((p4 ∨ (p4 ∧ p4)) ∧ (False ∨ True)) ∨ (p3 ∨ (p5 ∨ (p4 → ((p1 ∧ ((((p1 ∨ p1) ∨ False) ∨ False) ∧ (p3 ∨ (p3 ∨ False)))) → p4))))) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h10 =>
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- One of the premise coincides with the conclusion.
            exact h1
          case inr h13 =>
            -- False on the left can always be used.
            apply False.elim h13
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h15 =>
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- One of the premise coincides with the conclusion.
            exact h1
          case inr h18 =>
            -- False on the left can always be used.
            apply False.elim h18
    case inr h19 =>
      -- False on the left can always be used.
      apply False.elim h19
  case inr h20 =>
    -- False on the left can always be used.
    apply False.elim h20



