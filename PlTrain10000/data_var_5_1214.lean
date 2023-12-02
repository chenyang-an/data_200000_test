variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751642204120628746077467939533 : (((True ∧ (p3 ∧ ((((((p1 ∨ ((p4 ∨ False) → p1)) ∧ (p2 → p5)) → (p1 ∨ p4)) ∧ ((p3 ∧ p5) ∨ p1)) ∨ False) ∨ (True ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52986313353765230710875647834 : (((((p2 → p3) ∧ ((p2 → (p4 → p4)) → p1)) ∧ (p1 → p1)) ∧ ((p5 ∧ False) ∨ ((False → p5) ∧ (False ∨ (p3 ∧ (p3 ∧ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164859000542920704125922645885 : (((p1 ∨ ((p1 → True) → (True ∧ (p3 → (((p2 → (p4 → p5)) → p3) → p1))))) ∨ p4) ∨ ((p1 ∨ (((p4 ∨ True) ∧ p4) ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313932458855359615456628290045 : (p3 ∨ ((((p3 ∧ ((True → ((False ∨ p4) → (((True → p1) → (p2 ∨ p4)) ∧ p5))) ∨ ((p2 → p2) ∧ True))) → p2) ∨ True) ∨ (p5 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57675651554120020126138040184 : ((((p1 → p3) ∨ p3) → ((True ∧ (((p1 ∧ (p1 ∨ (p5 ∧ p2))) ∨ (True ∧ (True ∨ p4))) ∨ ((p3 → p4) ∨ p3))) ∨ (p1 ∨ p1))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42922512797996924008601162927 : (((p4 → ((((p4 ∧ ((p1 → (p5 ∧ ((p5 ∨ ((True ∨ p5) ∧ p2)) → p1))) → p2)) ∧ ((False ∧ p1) ∧ True)) ∧ p2) ∨ p4)) ∨ False) ∨ False) := by
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
theorem thm_5_vars_257279345924604126473538800755 : ((p2 ∨ p3) → ((p2 ∧ p3) ∨ (((True → p2) ∧ (((p3 → (p2 ∨ (p2 ∨ True))) ∨ True) → p3)) → (((False ∨ (p2 ∨ False)) ∧ p3) ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : ((p3 → (p2 ∨ (p2 ∨ True))) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- One of the premise coincides with the conclusion.
    exact h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h17 := h14 h16
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h17
    -- Conjunctions on the left can always be decomposed.
    let h18 := h13.left
    let h19 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h12
    -- Conjunctions on the left can always be decomposed.
    let h20 := h13.left
    let h21 := h13.right
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h22 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h23 := h20 h22
    -- One of the premise coincides with the conclusion.
    exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198970590651444196060161869340 : ((p5 → ((True → ((p1 → False) ∧ p5)) ∨ p3)) ∨ (p3 ∨ (((((p4 → False) → (((p1 ∨ p5) → (p5 → p2)) → p1)) → p3) ∨ True) ∨ p2))) := by
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
theorem thm_5_vars_178026896954407474848489096014 : (((p3 → ((p5 ∧ True) ∧ (False ∧ (p5 → (p1 ∨ (p4 → p4)))))) ∨ False) ∨ ((((False ∧ p4) ∨ p3) ∨ (((True → False) → p5) ∨ p2)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148132667217331710983665659483 : ((((True ∧ p1) → (((p4 → p2) ∨ False) ∨ (((p1 → p1) → True) → ((p2 ∧ True) → p1)))) → (p3 ∨ p4)) ∨ (False ∨ ((p4 ∨ p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717522547477852123439762933127 : ((((p2 → (p1 ∨ (False ∨ p2))) ∧ (True → ((((p3 ∧ (p4 ∨ p3)) ∨ (p5 → p4)) ∨ (True ∧ (p3 → (p1 → (p2 → p2))))) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118320057248675518491165719587 : ((p1 ∨ (p3 → (((p4 ∨ (p5 ∨ False)) ∧ (((False ∧ p3) ∧ p5) ∧ ((True ∧ (p4 ∧ p4)) ∧ p1))) ∨ ((p1 ∧ False) ∧ False)))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2592369885454781734238393435 : (((p1 ∧ p1) → ((p5 ∧ (True → p3)) ∨ False)) → ((False ∨ (p3 ∨ ((p3 ∧ p4) ∨ p4))) → (p1 → (p5 ∧ ((p4 ∨ False) → p5))))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h7 : (p1 ∧ p1) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h3
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h8 := h1 h7
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h17 : (p1 ∧ p1) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h3
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h18 := h1 h17
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h19.left
          let h21 := h19.right
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h22 =>
          -- False on the left can always be used.
          apply False.elim h22
      case inr h23 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h24 : (p1 ∧ p1) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h3
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h25 := h1 h24
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- Conjunctions on the left can always be decomposed.
          let h27 := h26.left
          let h28 := h26.right
          -- One of the premise coincides with the conclusion.
          exact h27
        case inr h29 =>
          -- False on the left can always be used.
          apply False.elim h29
  -- Implications on the right can always be decomposed.
  intro h30
  -- Disjunctions on the left can always be decomposed.
  cases h30
  case inl h31 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h32 =>
      -- False on the left can always be used.
      apply False.elim h32
    case inr h33 =>
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h34 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h35 : (p1 ∧ p1) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h3
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h36 := h1 h35
        -- Disjunctions on the left can always be decomposed.
        cases h36
        case inl h37 =>
          -- Conjunctions on the left can always be decomposed.
          let h38 := h37.left
          let h39 := h37.right
          -- One of the premise coincides with the conclusion.
          exact h38
        case inr h40 =>
          -- False on the left can always be used.
          apply False.elim h40
      case inr h41 =>
        -- Disjunctions on the left can always be decomposed.
        cases h41
        case inl h42 =>
          -- Conjunctions on the left can always be decomposed.
          let h43 := h42.left
          let h44 := h42.right
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h45 : (p1 ∧ p1) := by
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- One of the premise coincides with the conclusion.
            exact h3
            -- One of the premise coincides with the conclusion.
            exact h3
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h46 := h1 h45
          -- Disjunctions on the left can always be decomposed.
          cases h46
          case inl h47 =>
            -- Conjunctions on the left can always be decomposed.
            let h48 := h47.left
            let h49 := h47.right
            -- One of the premise coincides with the conclusion.
            exact h48
          case inr h50 =>
            -- False on the left can always be used.
            apply False.elim h50
        case inr h51 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h52 : (p1 ∧ p1) := by
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- One of the premise coincides with the conclusion.
            exact h3
            -- One of the premise coincides with the conclusion.
            exact h3
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h53 := h1 h52
          -- Disjunctions on the left can always be decomposed.
          cases h53
          case inl h54 =>
            -- Conjunctions on the left can always be decomposed.
            let h55 := h54.left
            let h56 := h54.right
            -- One of the premise coincides with the conclusion.
            exact h55
          case inr h57 =>
            -- False on the left can always be used.
            apply False.elim h57
  case inr h58 =>
    -- False on the left can always be used.
    apply False.elim h58



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193209582024713389740359593570 : (((p3 ∨ (p4 ∨ (True → p1))) → (p1 ∧ (p5 ∨ p4))) → (((p1 → (p3 ∨ p4)) ∧ True) → (p1 → ((p4 ∧ (True → True)) ∨ (p5 → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148761124846871780772267812288 : (((p3 → (((p1 ∨ p3) ∨ p2) → p4)) ∧ (((((p3 → p4) ∨ p2) ∧ (p4 ∨ p3)) ∧ (p1 ∧ p2)) ∨ p5)) ∨ (False → (p5 ∧ (p2 → p4)))) := by
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
theorem thm_5_vars_146808086991403461770954540182 : ((p4 → (((((False → p4) ∨ (False ∧ p2)) → (p5 ∧ (((p2 ∧ (False ∨ p3)) ∨ False) ∧ False))) ∨ True) ∧ p4)) ∧ ((p3 ∨ (p2 ∨ True)) ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115388994220777046634325877271 : ((((p1 ∨ p4) ∨ (p5 → ((False ∧ True) ∧ p2))) ∧ (p4 → ((p3 ∧ (((p3 ∨ (True ∧ p3)) → p5) ∨ (p4 ∨ False))) ∧ True))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325758629312565189577327421968 : (p5 ∨ (p2 ∨ (((p5 ∨ p1) ∧ (True → (p4 → (p4 ∧ p3)))) ∨ ((((p1 ∨ (p5 → p1)) ∧ ((p1 → p5) → p2)) ∧ p5) → (p4 → p1))))) := by
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
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197991866344473092768781839785 : (((p4 ∨ p5) ∧ ((True → (p4 ∧ p3)) → p4)) ∨ (((p3 ∧ (p5 ∧ p2)) ∧ p2) ∨ ((p5 ∧ True) ∨ (((p3 ∨ (p3 ∨ False)) ∧ p4) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321947487492212435752374415219 : (p5 ∨ (((((True ∨ ((False → p1) → (p2 ∨ (False ∨ True)))) ∧ p5) ∨ (p1 → ((p3 → p5) → p2))) ∨ (True ∨ ((p5 ∨ p1) ∨ p2))) ∧ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213714740776368663921234472026 : ((((False ∨ True) → p5) ∨ p5) ∨ (((p4 → (p5 ∧ p2)) → (p5 → ((p3 ∨ p3) → p3))) ∧ ((p5 ∧ (((False → p2) ∨ p2) → p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158475074694412422337060691632 : (((p5 → False) ∨ ((((p5 ∧ p3) ∧ p4) → ((((p3 ∨ p2) ∨ p4) ∨ False) → False)) ∧ (p3 ∧ p3))) ∨ (p4 → ((True ∧ p4) ∧ (True ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756560089515884081585916853528 : (((p1 ∧ (((((True ∧ p4) ∧ (True ∧ (((True ∧ True) ∧ (p2 ∧ True)) ∧ True))) ∨ p4) ∨ p3) ∧ (((p4 ∧ False) ∧ (p3 → p2)) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114739488194864027152910791728 : ((((p1 → (p2 ∧ p3)) ∨ (((False → p1) ∧ p3) ∨ (False → (p5 → (p4 → p3))))) → (((True → (p4 ∧ p5)) ∨ False) ∧ True)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60785735488707899032055197831 : ((True ∧ ((p3 → p2) → (p4 → (p5 → (True ∧ (((p5 → ((((p4 → (p5 ∧ p1)) → False) ∨ p2) ∧ p4)) ∨ p5) ∧ (p4 ∨ p1))))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226060220219279683155951314107 : (((p5 ∧ p3) ∨ p4) ∨ ((p3 ∨ ((((p1 ∧ (p5 ∧ p1)) ∧ p2) ∧ ((p5 ∨ p3) ∨ False)) → (False ∨ ((p1 ∧ p4) ∨ p1)))) → (p1 ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115708568419765020020709875315 : ((((False → (p1 ∨ (p4 → p5))) ∧ True) → (((p2 ∧ ((((p5 → ((p3 → p4) ∧ True)) ∧ p1) ∨ p3) → True)) → p5) ∨ True)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41607184627519666613198467449 : (((((p2 ∧ p2) ∧ (p1 ∨ (p1 ∨ (p3 ∨ p4)))) ∨ ((((((p1 → p3) → p4) ∧ ((p1 → False) ∧ p2)) ∨ p1) → p2) ∨ True)) ∨ p1) ∨ p1) := by
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
theorem thm_5_vars_316384971336295356694388036722 : (p3 ∨ (False ∨ (((False ∨ (False ∧ ((((p4 ∧ (True ∧ p5)) ∨ False) ∨ (p2 ∧ p3)) → p2))) ∨ True) ∧ (False → (p3 ∨ (p5 → (p3 → True))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148506288389801403748126835619 : (((p3 ∨ (p2 ∨ ((p1 ∨ (p5 ∧ ((p5 ∨ p3) ∨ p1))) ∨ p3))) ∨ (p3 → (((p4 → p2) ∨ p5) → p3))) ∨ (p4 ∨ ((p4 ∧ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299448816075022360489925699447 : (False ∨ ((p2 ∨ (p4 ∧ ((True ∧ (((p2 ∧ p5) → p4) ∨ (((p3 → False) ∧ ((p2 ∧ p5) ∧ False)) ∨ (p5 ∨ True)))) ∨ (p5 → p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799591078120303357131626810098 : (((p1 → (p4 ∨ (p2 ∨ (p4 → ((((p1 → (p1 ∨ ((p5 ∨ True) ∨ True))) → p3) → p5) ∨ ((((p5 → p2) ∧ p4) → p4) ∨ p2)))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156908175689540597385061285105 : (((((p2 ∨ ((p2 ∨ ((p4 ∨ True) ∧ p4)) ∧ ((False → (p1 ∨ True)) ∧ p3))) ∨ p3) → p2) ∨ p5) ∨ (((p2 ∧ (p2 ∧ True)) → True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53745076863857840893685750847 : ((((((p3 ∨ True) ∧ ((p3 → p3) ∧ True)) ∧ p4) ∧ True) ∨ (p1 ∧ ((((p2 ∧ (False ∨ (p5 → p3))) ∧ True) ∧ p2) → (p5 ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228109868597629425748990489953 : ((p4 ∧ (p4 ∨ False)) ∨ (p4 ∨ ((p5 → ((((p5 ∨ ((p2 ∨ (p4 ∨ ((p3 ∧ p1) ∨ True))) ∧ True)) → p3) ∧ False) ∨ (True ∧ p4))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172001975227218675551704111605 : (((((p1 ∨ (True ∨ p5)) → (((p1 ∨ p5) → False) ∧ p3)) → p5) ∨ (False ∨ False)) ∨ ((((p3 ∨ True) ∧ p5) ∨ (p2 ∨ p2)) → (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151222890785496248869149690943 : (((((p5 ∧ p3) ∧ False) ∨ (p2 ∨ (p5 → (((((p5 → p1) ∧ p3) → (p2 → p3)) → p2) ∧ p3)))) → True) → (p4 → (p3 ∨ (p1 ∨ True)))) := by
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
theorem thm_5_vars_111686578141067937011138865944 : (((((((p4 ∧ (False → ((p1 ∨ p4) ∧ (True ∨ p5)))) ∧ (((p3 ∧ p3) ∧ p5) → p5)) → (True ∨ False)) ∨ p3) → False) ∨ False) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358661115289667632613510629094 : (p5 → (p4 → (((((p1 ∨ p1) ∨ False) ∨ p1) ∧ (((p3 ∧ p5) → ((p4 ∨ p4) → False)) ∨ p1)) ∨ (True ∧ (p1 ∨ (p2 → (p4 → True))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98810704846188695434682305773 : ((True → (((True → (((((p4 ∨ False) ∧ (p1 ∨ p2)) → (False ∧ p5)) ∨ p2) ∨ p1)) ∨ (p3 ∧ ((p2 → p1) → (p4 ∧ p5)))) ∧ False)) → p4) := by
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
theorem thm_5_vars_116663361745499513925282501569 : (((p4 → p2) ∧ ((p2 ∧ (((p4 ∧ ((p3 ∧ p2) → p1)) ∨ (p3 ∧ (p5 ∧ False))) ∨ (((False → p5) ∧ True) → p3))) ∨ False)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230875008500912671524598172735 : (((p2 ∧ True) ∨ True) → (((((((p1 → ((p2 → p5) → True)) ∨ (p2 ∨ (p3 ∧ p3))) ∨ p3) → p2) ∧ (p4 → (False ∨ p1))) ∧ p2) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158151482858250569226892196039 : (((False ∨ ((False → p3) → p2)) ∨ (((((p4 ∧ False) ∨ (p1 ∧ p4)) ∨ p3) ∨ False) ∨ (True ∨ p2))) ∨ (False ∧ (p2 → (p5 ∧ (True ∨ True))))) := by
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
theorem thm_5_vars_322358594038269912788661843479 : (p5 ∨ (((p3 ∧ (p5 ∨ ((((p4 → False) ∨ p2) → (p5 ∨ (False → p3))) ∨ ((True ∧ p1) → (p4 → p5))))) ∨ ((p4 ∨ False) → True)) ∨ p2)) := by
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
theorem thm_5_vars_175353976685431616991061945011 : ((p5 ∨ (((p3 ∧ p3) ∨ p5) ∨ ((p5 ∨ p3) ∨ (((True ∨ p4) → p5) → p1)))) → ((p1 ∨ ((p1 → False) → True)) ∧ (False ∨ (True → True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h20 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h21
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h27
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h28 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h29
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h32 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h33
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h34 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h35
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h36 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h37
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77425367284645629586952837115 : ((((p4 → p2) ∨ ((True → False) → (p3 → ((p2 ∨ p2) → ((False ∧ (False ∨ p3)) ∨ ((p3 ∨ p2) ∧ ((p3 ∨ p4) ∧ p3))))))) → False) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 → p2) ∨ ((True → False) → (p3 → ((p2 ∨ p2) → ((False ∧ (False ∨ p3)) ∨ ((p3 ∨ p2) ∧ ((p3 ∨ p4) ∧ p3))))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h8 := h3 h7
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h11 := h3 h10
      -- False on the left can always be used.
      apply False.elim h11
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h2
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336295725536492805919923110655 : (p1 → (((p2 ∧ (p1 ∨ (True ∧ (p4 ∧ (p5 ∧ p3))))) → (True → (p4 ∧ ((((False ∨ p1) ∧ (False ∨ p5)) → p5) → (p2 ∧ p5))))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217672092760854824975643925905 : ((((True → p1) → p1) → False) → (p4 ∨ ((p3 ∧ (p4 → p3)) ∨ (p4 ∧ ((((p4 → p3) ∨ (p5 ∨ p3)) ∧ (p4 ∧ (p3 ∨ p5))) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True → p1) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350695104009137832104024009480 : (p4 → ((p4 ∧ (((((p5 → p1) ∧ (p3 ∧ False)) ∧ (((p5 → (p3 → True)) ∨ p5) ∨ p5)) ∨ ((True → p5) ∧ (False → p4))) ∧ p1)) → p5)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h17 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h18 := h15 h17
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40334638286402227701721346819 : ((((((((p2 ∧ ((p1 → (p5 → False)) ∧ p3)) ∨ (p1 ∨ p4)) ∨ p5) ∨ ((p1 ∨ p5) ∧ ((p3 → p3) → p3))) ∨ True) ∨ p1) ∨ p4) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619437643530651182265428473969 : (((((True ∨ (True ∧ p3)) → ((p4 ∨ (((p1 → p1) ∧ ((False ∧ (p5 → p5)) ∧ p3)) ∧ ((p2 ∧ p5) → p3))) ∨ (True ∨ p3))) ∨ p4) ∨ p4) ∧ True) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254252313779419683945928705218 : ((p2 ∧ p2) → (False ∨ ((p5 → ((p4 ∧ ((False → p4) ∧ p2)) ∨ (((p1 → (p5 ∨ p1)) ∧ ((p3 ∨ (p2 → p2)) ∧ False)) ∨ p4))) ∨ True))) := by
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
theorem thm_5_vars_260750343930764298249806768513 : ((p3 → p4) → (False ∨ ((((((p4 → (p3 ∨ p4)) → (False → ((p5 ∨ (p1 ∧ p2)) → False))) → p2) ∧ p5) ∨ (p4 → (False → False))) ∨ p2))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118222814579235447319012277251 : ((p1 ∨ (((((p5 ∨ (p3 ∨ (p5 ∧ p3))) ∨ True) ∧ p4) → ((((p5 ∧ (p4 → (p1 → p2))) ∨ p3) ∧ p1) ∧ False)) ∨ p4)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305488978122361235205948176174 : (p1 ∨ (((p3 ∧ (False ∨ (True ∧ ((p3 ∨ ((p1 ∨ p5) ∨ False)) ∧ p4)))) ∧ p1) ∨ ((True ∨ True) ∨ (True ∨ ((p3 → p3) ∧ (p1 ∧ p4)))))) := by
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
theorem thm_5_vars_40480595919558631129161291068 : (((((p4 → p3) ∧ ((p4 ∧ True) ∨ ((p4 ∧ p5) ∧ (p4 ∨ ((((p3 ∨ p1) ∧ False) ∧ (p5 → (True ∧ p2))) ∨ p1))))) ∨ p5) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51380392508004759885988071315 : ((((((((p3 ∨ (p3 ∨ ((p3 → p4) ∧ False))) ∧ False) ∨ p1) → p2) → (p4 → p3)) ∨ p1) → ((True → p4) → (p3 ∧ (p2 → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345551256977276988512017189615 : (p3 → (((((True ∨ p2) → False) ∧ (p2 ∨ False)) → ((((p1 ∧ False) ∨ ((p1 ∧ ((p4 → p4) → p1)) ∨ (p5 → p4))) ∨ p1) ∨ p3)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356342252548554372557382957408 : (p5 → ((((p5 ∨ p4) → ((p5 ∧ p5) ∧ ((p5 ∨ (True ∨ p1)) ∨ p4))) ∧ p3) ∨ (p4 ∨ ((p1 → (True → ((p4 ∨ p2) ∧ p4))) ∨ p5)))) := by
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
theorem thm_5_vars_179536366558476993098336202442 : ((p1 → ((((p3 ∨ (p5 → p3)) → p5) ∧ (p3 ∨ True)) ∨ (True ∨ p5))) ∨ ((p4 → (p5 ∨ p2)) ∧ ((True → p4) → ((p3 ∨ p2) ∨ p3)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166167707243832401897885453466 : ((False ∧ ((p4 ∨ p5) ∨ ((p4 ∨ p4) ∨ ((p5 ∨ ((p5 ∨ p1) ∨ (True ∨ p1))) ∨ False)))) ∨ ((p3 → True) ∧ (True ∨ (False ∧ (p4 ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65286638080628929791225345863 : ((p3 ∨ ((((p3 ∧ ((((p1 ∧ ((False ∨ p2) → ((False ∧ p2) → p4))) ∨ True) → True) → True)) ∧ (p5 ∨ p3)) ∨ False) ∨ (p3 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59684228868248395607979809194 : (((True ∧ p4) → (((True ∧ ((p4 ∨ p5) ∧ p3)) ∨ (True ∧ (p4 → (True ∨ p4)))) → ((((p2 ∨ p2) → (p4 ∧ p2)) ∧ False) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180982113052529515435465197825 : (((True ∧ p4) ∨ (((False → (p3 → p2)) → p1) → ((p1 ∨ p3) → p4))) → (((((p4 → p4) → p5) ∨ p3) ∧ ((p3 ∧ p5) ∧ p3)) → p5)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h4.left
    let h16 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h22 =>
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164922473689098645654566015061 : (((((((((p5 ∧ p3) → (p2 ∨ p4)) → True) ∧ p2) ∨ (p3 ∨ True)) → False) ∨ p1) → p5) ∨ (((p1 ∧ p3) → p5) ∨ (p1 → (False → p1)))) := by
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
theorem thm_5_vars_347288767918011604720744933626 : (p3 → ((((p3 → p2) → p1) → (p1 ∨ (p2 ∧ (p3 ∨ p5)))) ∨ (((p3 ∨ True) → (p4 ∨ (False → p1))) ∨ (p4 ∨ (p4 → (p2 → p2)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356727087304923093053877950978 : (p5 → (((p1 ∧ (p3 ∨ True)) ∧ (p1 ∧ p2)) ∨ ((p4 ∧ ((((p2 ∧ (p5 ∨ p3)) ∧ False) → (p3 ∨ p3)) ∨ True)) → (p2 ∨ (False → False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46898906238437219942677185719 : ((((((p2 ∨ (((p3 → (p4 ∨ (((p2 ∨ p5) ∧ p2) ∨ p1))) ∧ (p4 → p4)) → p1)) ∧ True) ∧ (p4 ∨ p5)) ∨ p2) ∨ (p1 → p1)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136522241677807900835270625485 : (((p3 ∨ (p5 ∨ p1)) ∧ (((p3 ∨ (((True ∨ (p3 ∨ p4)) ∧ True) → p4)) ∧ (p4 → p2)) ∨ ((p3 ∧ p1) → p5))) ∨ ((False → p3) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352372606483511431839694070649 : (p4 → (((p2 ∧ p2) ∧ p5) ∨ (((((p1 → (True ∧ (p1 ∧ p4))) ∧ p4) ∨ (p1 ∨ p4)) ∧ p2) → (p1 ∨ (((p4 ∨ p3) → False) → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : (p4 ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h15 : (p4 ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h16 := h14 h15
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56978602726130257115261415097 : (((p4 ∨ (p5 ∧ p2)) ∧ ((((p4 ∨ (False → (True → p4))) ∧ (True ∨ p4)) ∨ (((True → p4) ∧ p4) → (True → (p1 ∨ p3)))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51427918075761197019370293322 : ((((False ∨ (((True → p5) → p4) ∨ (((p4 → p4) → p5) → (p3 ∧ p2)))) ∧ (p4 ∨ True)) → ((((p3 → True) ∨ False) → p2) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172252174254215561284356091059 : (((True ∨ (p3 → (True → (p3 ∨ (p2 → p5))))) ∧ (p2 ∧ (p5 ∨ (p1 → False)))) ∨ ((((True → False) ∧ p2) ∨ ((p3 → True) ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112188337796354296769942932877 : (((p5 ∧ ((p2 ∧ ((p1 ∨ (((p1 ∨ (True ∨ (False → False))) ∧ False) → False)) ∧ p4)) ∧ ((p2 ∧ p2) → (p1 ∨ p5)))) ∨ p1) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340817934377308803210572761987 : (p2 → (((((True → ((False → p3) ∨ ((p3 → p1) ∨ ((((p4 → p1) → True) → (p1 ∧ p3)) → True)))) → p5) ∧ p5) ∨ (True ∨ p2)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49002266999496293388174927131 : ((((p4 → (((True → p1) → p2) → (((p2 ∨ (p2 ∨ (p4 → ((p4 ∧ p3) → p1)))) → p2) → p3))) ∨ p1) ∨ ((p5 ∨ False) → p5)) ∨ p4) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165324234386093450848008695649 : (((((p4 ∧ (p4 ∧ (p3 ∧ (p4 ∨ p3)))) ∨ (p3 → p1)) ∧ p2) ∧ ((p1 → p2) ∧ False)) ∨ ((p2 → (False ∧ p4)) → ((p4 ∧ p2) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225440850851414096105946876349 : (((p3 ∨ p5) ∧ p3) ∨ ((p4 ∧ (((p1 → (((False → p5) ∨ p2) ∧ (p1 ∧ p3))) ∨ ((p5 ∨ p3) ∧ (p4 → p2))) → False)) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807243139945140502115071128177 : (((p4 → ((((((((p5 ∨ p5) ∧ True) ∧ p5) ∧ p4) ∨ (False → p2)) ∧ p3) ∧ p4) ∨ ((p3 ∨ p4) ∧ (p3 → (False → (p4 → True)))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192631818952837702681421807545 : ((((((p1 ∧ True) ∧ (p1 → False)) ∨ p1) ∨ p2) → False) → ((((False ∧ p2) ∨ ((p3 ∧ (p3 ∨ ((p2 ∨ False) ∧ p5))) ∨ p3)) ∨ True) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67376969298202732878679052454 : ((p1 → ((((p1 → ((p4 ∧ p2) → (((False ∨ p1) ∨ p2) ∨ True))) → ((p3 → p4) ∧ p4)) ∨ (p5 ∨ ((p5 → p1) → p2))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186584668601139299309538946795 : ((((p3 ∧ ((p5 → (False ∨ p3)) ∨ p2)) ∧ p5) → (p5 ∧ False)) → (((p1 ∨ (p1 → (True ∧ True))) → p4) ∨ ((p4 → p4) ∧ (True ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138145715650385216690273700117 : ((p1 → (((p3 → (((((p4 ∨ p4) ∧ (((False ∨ p2) → True) ∨ p4)) → p2) ∨ (p5 ∧ False)) ∨ p2)) ∧ True) ∨ p3)) ∨ ((True ∨ p1) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225392136957460054756738491990 : (((p2 ∨ p3) ∧ p5) ∨ ((True → False) ∨ ((((p3 → p1) ∨ ((((p2 → True) → p5) ∧ p2) ∨ (False → p5))) → False) → (False ∨ (p2 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 → p1) ∨ ((((p2 → True) → p5) ∧ p2) ∨ (False → p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44361390043158746226147288208 : ((((((p3 → p3) ∨ (p4 ∧ (p1 ∧ (p1 → ((p3 ∧ p2) ∧ p1))))) → p3) ∧ (p4 ∧ (False → ((p1 ∨ p4) → (p4 ∧ True))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351682262095316241680787469455 : (p4 → ((p2 ∨ (((p4 → (((p2 ∧ p3) → p4) ∧ ((p3 → p3) ∨ p2))) → p2) → p2)) → ((((True ∨ p4) → True) → (p5 ∨ p3)) ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137646918563030746732816075843 : ((False ∨ (((False → (True ∨ False)) → p4) ∧ (((p4 ∧ True) → ((p3 ∨ p4) → (p3 ∨ p3))) ∧ (p4 → (p1 ∧ p4))))) ∨ (False → (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40511024605604818593898625370 : ((((p3 ∧ ((((((True ∧ (p4 ∧ (p1 → p4))) ∨ ((p5 ∧ p1) ∧ (p3 → p3))) → p5) → (p3 → p5)) ∨ True) → p1)) ∨ p2) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751136542951880974902351793 : ((((p3 → p1) → p3) ∨ (p2 ∨ ((False ∨ p5) ∨ (((p5 ∧ (p2 ∧ (p3 ∨ (p4 ∧ p3)))) ∧ True) → (p3 → (p1 ∨ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98921814881809132929578879405 : ((True → ((p5 → ((p3 → (p4 → ((((((p2 → p5) → False) → (False → (True → p3))) ∧ False) ∧ p2) ∧ False))) ∨ True)) ∧ (True → False))) → p3) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218069232561200288756125356282 : (((p4 ∨ p4) ∧ (True → False)) → ((p2 ∧ p2) ∨ ((((False ∧ (True → True)) ∧ (((True ∧ p5) ∧ ((p5 ∧ p1) → p1)) ∨ p5)) ∧ p5) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114180000393735904846747833857 : (((((p3 ∨ ((False → p4) ∧ (False ∧ ((p4 ∨ (p2 ∨ True)) ∨ p4)))) ∧ p4) ∧ ((False ∨ p4) ∧ True)) → ((p5 ∨ p2) → p1)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48716324150425670531513244482 : ((((((p3 ∨ p2) ∨ p1) ∨ p5) ∨ ((p2 → (((((p3 ∧ p4) ∨ p4) ∧ True) → True) → (p2 → True))) ∧ p5)) ∧ (p4 ∨ (p5 → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116826929501798007892646604211 : (((p5 ∨ p1) ∨ ((((p1 ∨ p1) ∨ (p5 ∧ p5)) ∨ (((p4 ∨ p3) ∨ (((False → p3) → p2) → (p3 → p3))) ∧ p3)) ∧ p1)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782038032481604114066453748607 : (((p2 ∨ (p5 → ((p2 ∧ ((p2 ∨ (True ∨ (False → True))) → p1)) ∨ (((p5 ∧ False) ∨ (p5 ∨ (True ∧ (False → (p1 ∨ p1))))) ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68462093111192929263798997384 : ((p3 → (p3 ∧ ((((((p4 ∨ (True → False)) ∨ True) → True) ∧ ((((p1 → p5) → p1) ∨ True) → (p4 → (p5 ∨ p4)))) → p5) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112111071517608697157660154851 : ((((True → p4) → ((((p3 → ((p5 ∨ (True → p4)) → (True → (((p5 → p1) ∧ False) → p1)))) ∧ p3) ∨ False) ∧ False)) ∨ True) ∨ (p1 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354598218056305315034241582868 : (p5 → (((((((((p2 ∧ p3) ∧ p5) ∧ p1) ∧ (p4 ∨ (True ∨ (True ∨ p5)))) ∧ (p1 → (True ∧ False))) ∨ (p3 ∨ p4)) ∧ p3) ∨ True) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134668187040858168895696872401 : ((((((((p4 ∧ False) ∨ p4) → False) ∨ p4) → p5) ∧ ((p1 ∧ p1) → ((p3 → (p2 ∨ (p3 ∧ p3))) ∧ p2))) → p4) ∨ ((p3 → False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684911891500918108074869636724 : ((((p1 ∧ ((((((False ∧ (p3 ∨ p4)) → p5) ∨ p1) ∧ (p1 ∨ (p2 ∧ True))) → p5) → p5)) ∨ (((p1 ∧ p5) → p5) ∧ (True → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



