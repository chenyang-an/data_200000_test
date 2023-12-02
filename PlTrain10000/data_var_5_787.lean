variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114157004871689318895024287870 : (((((((True ∧ (p5 ∨ (True ∧ ((p3 ∨ p2) → False)))) → False) ∧ ((True ∨ False) ∨ p3)) ∧ p1) → True) → (True ∧ (p3 ∧ p3))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617848842422803443797761865001 : ((((((p2 ∧ (p2 ∨ (True → p4))) → p3) → (p1 ∧ ((p4 ∨ p2) ∨ ((p5 → (True ∧ ((p3 ∨ True) ∧ (p3 ∨ p4)))) ∨ False)))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187766864013620433126667452579 : ((p2 → (p5 ∧ (False ∧ ((p2 ∧ (p2 ∨ (True ∧ p1))) ∨ p2)))) → (((p3 → p1) ∧ ((((p4 ∨ (p5 ∨ True)) ∨ p4) ∧ p4) ∧ p5)) → p5)) := by
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
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h6
  case inr h14 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230378907862997841204555228791 : (((p3 ∨ p1) ∧ p4) → (((True ∧ ((p2 ∨ False) ∨ (p2 ∧ True))) ∧ p4) ∨ ((False → ((p5 ∨ p3) ∨ (True ∧ p1))) → (p1 → (True ∨ True))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230609825582379264683401220258 : (((p2 → False) ∧ p4) → (p4 → (((p1 → (False → p3)) → True) ∧ ((((False ∨ p1) ∧ (p3 → (p3 → (p2 ∧ True)))) ∨ p4) ∨ (False → False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58133128748618771436598598232 : (((p2 ∧ p1) ∧ ((p5 → (p5 → p5)) → (p3 → ((((p3 → p5) ∨ p5) ∧ ((((p2 ∨ (p5 ∧ p4)) ∧ p5) → True) ∨ p4)) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245433141656148717889162483314 : ((p2 ∧ p4) ∨ ((True ∨ (True ∨ p5)) ∧ ((((p3 ∧ (((p4 ∧ p3) ∨ (False ∧ p1)) ∧ (p4 ∧ (p4 → p3)))) ∨ p4) ∨ p1) ∨ (False → p4)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232332126137640556187540641287 : (((p4 → True) → False) → (((((p5 ∨ p5) ∧ p1) ∧ (p5 ∧ ((((p2 → p2) ∨ p4) ∨ (p1 ∨ (True → p4))) → (p1 ∧ p5)))) ∧ False) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p4 → True) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (p4 → True) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h8
  -- False on the left can always be used.
  apply False.elim h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h14 : (p4 → True) := by
        -- Implications on the right can always be decomposed.
        intro h15
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h16 := h1 h14
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h18 : (p4 → True) := by
        -- Implications on the right can always be decomposed.
        intro h19
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h20 := h1 h18
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h23 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h24 : (p4 → True) := by
        -- Implications on the right can always be decomposed.
        intro h25
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h26 := h1 h24
      -- False on the left can always be used.
      apply False.elim h26
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h29 : (p4 → True) := by
        -- Implications on the right can always be decomposed.
        intro h30
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h31 := h1 h29
      -- False on the left can always be used.
      apply False.elim h31
    case inr h32 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h33 : (p4 → True) := by
        -- Implications on the right can always be decomposed.
        intro h34
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h35 := h1 h33
      -- False on the left can always be used.
      apply False.elim h35
  case inr h36 =>
    -- Disjunctions on the left can always be decomposed.
    cases h36
    case inl h37 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h38 : (p4 → True) := by
        -- Implications on the right can always be decomposed.
        intro h39
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h40 := h1 h38
      -- False on the left can always be used.
      apply False.elim h40
    case inr h41 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h42 : (p4 → True) := by
        -- Implications on the right can always be decomposed.
        intro h43
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h44 := h1 h42
      -- False on the left can always be used.
      apply False.elim h44
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h45 : (p4 → True) := by
    -- Implications on the right can always be decomposed.
    intro h46
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h47 := h1 h45
  -- False on the left can always be used.
  apply False.elim h47
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h48 : (p4 → True) := by
    -- Implications on the right can always be decomposed.
    intro h49
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h50 := h1 h48
  -- False on the left can always be used.
  apply False.elim h50



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_517818255805277794772463458925 : ((((p1 ∧ p5) → (((p3 ∨ (p2 → False)) ∨ p2) → (True ∧ ((False ∨ (p5 ∨ p1)) → ((((p1 ∧ p3) ∧ p1) ∨ False) ∨ (p1 ∧ p5)))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Conjunctions on the left can always be decomposed.
          let h9 := h1.left
          let h10 := h1.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h9
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h1.left
          let h13 := h1.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h12
          -- One of the premise coincides with the conclusion.
          exact h13
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h1.left
        let h16 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h15
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h1.left
          let h21 := h1.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h20
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h22 =>
          -- Conjunctions on the left can always be decomposed.
          let h23 := h1.left
          let h24 := h1.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h23
          -- One of the premise coincides with the conclusion.
          exact h24
      case inr h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h1.left
        let h27 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h26
        -- One of the premise coincides with the conclusion.
        exact h27
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165010574383353491513631211227 : ((((((p5 → (True → p3)) ∨ p4) ∨ False) → ((p1 → (p1 → True)) → (False → p2))) → p1) ∨ ((True ∨ (False ∧ ((p2 ∨ p3) → p2))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198945495409076043526450710148 : ((p4 → ((False ∧ p2) ∨ (p2 ∨ (p5 ∧ False)))) ∨ (((p2 ∧ False) → (True ∨ ((p2 ∧ False) ∨ (p3 → p2)))) ∨ ((p3 → (p5 ∨ p3)) ∨ p3))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185111880756236415083175687501 : (((p3 → p4) ∨ (p3 → ((False ∧ p1) ∨ (p4 → (p3 ∧ False))))) ∨ (((p3 ∨ p2) ∧ True) → (p1 ∨ (p3 ∨ (p2 ∨ (p2 ∨ (p5 → p5))))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8577823649343994427413600940 : (((((p4 ∨ (p2 ∨ (p2 ∧ ((p4 ∨ ((False ∧ (p3 → (False ∧ (p2 ∧ False)))) ∨ (p2 → p3))) → p1)))) ∨ p3) ∨ (True ∨ p3)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_137674774553962200497910949135 : ((False ∨ (p4 → ((p5 → (p3 → p3)) ∧ (((p5 ∨ (p1 ∧ (p2 ∨ (False ∨ p4)))) ∨ (p5 → (True ∧ True))) ∨ p3)))) ∨ (p2 ∧ (p2 ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654256503795026315343452734421 : (((((((((p5 ∧ (((p5 ∨ p1) ∧ (True ∨ (p2 ∨ p3))) ∨ p5)) → p1) ∨ (p1 → p5)) ∨ True) ∧ (False → p5)) ∨ True) ∨ (p1 ∧ p1)) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321240817629679605952076150813 : (p4 ∨ (p4 ∨ ((p3 ∨ (((True ∨ (p3 → p5)) ∧ (((p4 ∨ True) ∨ (((p1 ∨ (p3 ∧ p5)) → p3) → p1)) → p3)) ∧ (p1 → p1))) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h9 : ((p4 ∨ True) ∨ (((p1 ∨ (p3 ∧ p5)) → p3) → p1)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h10 := h7 h9
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h12 : ((p4 ∨ True) ∨ (((p1 ∨ (p3 ∧ p5)) → p3) → p1)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h13 := h7 h12
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52745868347211002264882774161 : ((((p2 ∧ ((((p1 ∨ p1) ∧ ((False ∧ p1) → p2)) ∨ p2) ∧ p3)) ∨ p2) → ((((True ∨ (p1 ∨ (p2 ∨ p2))) → p1) ∧ True) ∨ True)) ∨ p2) := by
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
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
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
theorem thm_5_vars_255899632792060569912285407462 : ((True ∨ p1) → (p2 → ((False ∧ p1) ∨ ((((True ∧ (p1 ∧ p2)) ∨ (((p1 → p3) ∨ p5) ∧ p4)) ∨ ((True ∧ (True ∧ p3)) → p2)) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h9
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685640170412925882949787767971 : (((((((p4 → (((p2 ∧ p2) ∨ False) → p1)) ∧ True) ∧ (p4 ∧ (p2 ∨ (p5 ∨ p5)))) ∨ p5) → (p3 → (((p2 ∨ p1) ∨ p5) ∨ p5))) ∨ p4) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h5.left
    let h9 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218091534669948011837854984826 : (((True → p4) ∧ (p2 → p3)) → (p5 ∨ (((p3 ∨ True) ∧ (((p5 ∨ (((p1 ∧ p4) → p4) ∧ p3)) ∧ p5) → ((p1 → p4) ∨ True))) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306465184185751902082889312477 : (p1 ∨ ((p5 ∨ False) ∨ (False ∨ (p4 ∨ (False → ((((((p5 ∨ False) → p3) → p1) ∧ ((p3 → p5) ∧ p4)) ∨ (p3 ∧ p5)) ∨ (p2 → p1))))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303938155883040164663224754517 : (p1 ∨ (((p1 ∨ ((False ∨ (p3 ∧ False)) → p2)) ∧ ((((((p1 ∧ p3) ∨ p4) ∧ p2) → p3) → p3) ∨ (p5 ∨ (False → (p5 ∨ p3))))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127730451773969676436086302522 : ((True → ((((p1 ∧ False) ∧ p5) ∨ (((p2 → ((p4 ∧ p1) ∨ ((p4 ∨ ((p2 ∨ p4) ∧ p3)) → p4))) ∧ p3) ∧ p2)) ∧ p3)) → (False ∨ p4)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h15 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h16 := h13 h15
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h20 =>
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h21 : (p4 ∨ ((p2 ∨ p4) ∧ p3)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h22 := h20 h21
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137104039796253870068335932276 : ((True ∧ ((((False ∨ p1) ∧ (p3 → (p4 ∧ p5))) ∨ (((p5 → (p3 ∧ False)) → (False ∨ p4)) ∨ p4)) → (True ∧ p5))) ∨ ((False → p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609751251183666346089872593546 : (((((p4 ∨ (((p2 ∨ p4) → ((((p3 ∧ p5) ∨ (p3 ∧ p4)) → (p4 ∧ (p4 ∧ p5))) ∨ p2)) ∨ (p5 ∧ (True ∨ p3)))) ∨ True) ∨ p5) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191818123106957158783113037060 : ((p2 ∨ (p2 ∨ (p5 ∨ (p4 ∨ (p5 ∧ (True ∧ p4)))))) ∨ (p3 → (p4 → ((p1 → (False ∨ ((True ∨ p1) ∧ p4))) → (p2 → (p5 → p3)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198241964397522439316502190738 : ((True ∧ (p4 ∧ (((p3 ∧ p1) ∨ p1) ∧ False))) ∨ (p1 → ((p1 ∧ ((False → ((p4 → (p5 ∨ p2)) ∨ (p4 → True))) → True)) ∨ (p2 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116338996391916325519186459478 : ((((p5 → True) ∧ p2) → ((p2 ∧ p3) ∨ ((((p3 ∧ ((p3 ∨ (p5 → (p1 ∨ (True → p4)))) → p3)) → True) ∨ False) → False))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135886281230421476657573324484 : (((p4 ∨ (((((p5 ∧ p3) ∧ p3) → (p1 ∧ p3)) ∧ p3) ∨ p3)) ∨ (((p3 ∧ False) ∨ (p2 → (p2 ∧ p5))) ∨ True)) ∨ (True ∧ (p5 ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46833059828910808084826796022 : (((((p2 ∨ ((p2 ∧ p1) ∨ ((p1 ∨ p5) ∨ (((True → False) ∨ p1) ∨ p3)))) ∨ ((p3 ∨ (p2 ∨ True)) ∧ False)) ∧ False) ∨ (True ∨ False)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613685950155476999547951639365 : (((((((((True ∧ p2) ∧ p1) ∨ p1) → p5) → ((p3 ∨ p2) ∧ (((False → (p4 → False)) → p4) ∧ p2))) ∧ (p5 → (p3 → p2))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_707281061539530931878132018479 : (((((p2 ∨ ((p3 ∧ p1) ∨ p4)) ∧ (True ∨ p1)) ∨ ((True ∨ (False → ((p2 → False) → p4))) ∧ (((p3 ∧ p5) ∧ (True → p1)) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42821028718388203331660879119 : (((p1 → ((p2 ∨ (((False → p1) ∨ p3) ∧ (p4 ∧ p2))) ∧ ((p3 ∧ ((((True → True) → (p1 ∧ p1)) ∨ False) → p1)) ∧ p1))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232199700071370343656676010182 : (((False → p3) → p3) → (((p2 ∧ False) ∧ ((((p1 ∨ p3) ∨ (p4 → ((True ∧ p4) ∧ True))) ∧ (p1 → (p4 ∨ (p5 ∧ p5)))) ∧ p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156944083761967775683843853757 : ((((((p4 ∨ ((True ∧ p3) ∨ p5)) → ((True ∧ (p2 → p4)) → p5)) ∧ True) → (p5 ∨ False)) ∨ True) ∨ ((p4 → (p1 ∧ (p4 ∨ False))) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46960745901905397677609892708 : (((((True → (p5 ∨ ((((((False → (False ∨ (True ∧ p3))) ∧ False) ∧ (True ∨ p4)) ∧ True) → p2) ∨ p5))) ∧ p1) → p5) ∨ (True ∨ p4)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46508915981527365465294811406 : ((((p4 ∧ p4) ∧ (((p3 ∧ (p5 ∧ p2)) ∧ ((p5 ∨ False) ∨ (True → ((p2 → p2) → True)))) ∧ ((p5 ∨ p5) ∨ False))) ∧ (True → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697923733784460678095791916810 : ((((((p3 ∧ True) ∨ ((p3 ∨ p4) → (p4 ∧ (p4 ∨ p1)))) ∧ True) ∨ (False ∧ (((p2 ∨ (False ∧ p3)) ∨ (p4 → (False ∨ p2))) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227145214020762999578242969917 : (((p5 ∨ False) → p4) ∨ (((((p4 → (p1 ∧ True)) ∧ (p1 → (p5 ∧ False))) ∧ (((p4 ∧ p2) ∨ ((True ∧ True) ∨ p5)) ∧ p4)) → p2) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h15 : p1 := by
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h16 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h17 := h4 h16
        -- We need to get the left conjuct of h17 based on <expert-advice>.
        let h18 := h17.left
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h19 := h5 h15
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h22 : p1 := by
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h23 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h24 := h4 h23
        -- We need to get the left conjuct of h24 based on <expert-advice>.
        let h25 := h24.left
        -- One of the premise coincides with the conclusion.
        exact h25
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h26 := h5 h22
      -- We need to get the right conjuct of h26 based on <expert-advice>.
      let h27 := h26.right
      -- False on the left can always be used.
      apply False.elim h27
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337144972270469682240501881443 : (p1 → ((p1 → ((True ∧ (p4 ∧ p3)) ∨ (p2 → (p4 ∨ ((p3 ∧ (p5 → p5)) ∨ ((((p3 → False) ∨ p1) → p3) ∧ p3)))))) ∨ (p4 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697408127049649241196666488534 : ((((True ∧ (p5 ∧ ((((True ∨ (p1 ∧ False)) → p1) ∨ False) → p4))) ∧ (((p3 ∧ p3) ∧ (((p1 → p2) ∨ p3) ∨ p5)) → (False ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115233796526374517296206550231 : ((((False ∧ ((p4 ∨ p3) → (False ∨ (p1 ∧ False)))) ∨ p2) ∨ (True → (((((p2 ∧ p2) ∧ p3) ∧ p3) ∧ (False → p1)) ∨ p4))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186684102905161792843312209320 : (((p4 ∨ ((True → (p5 → True)) ∨ p4)) ∧ ((p2 → True) ∨ p1)) → ((p1 ∨ ((p3 ∨ ((p1 ∨ True) ∧ ((p5 ∧ True) ∧ True))) → False)) ∨ True)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
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
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
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
theorem thm_5_vars_41477851050177662965145500823 : (((((((p4 ∨ p3) ∧ p2) ∧ p3) ∨ (((p1 → p4) ∧ False) ∨ p1)) ∨ ((p1 ∨ (False → (p4 ∨ False))) ∨ ((p2 → False) ∧ p2))) ∨ p2) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168591703031991558424546808640 : ((p2 ∧ (p5 ∧ ((p3 → p4) ∨ ((p1 ∨ ((p1 ∧ False) → ((p1 ∧ p4) → False))) ∧ p2)))) → ((p1 ∨ ((p3 ∨ (p4 ∧ True)) ∨ p2)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
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
      -- One of the premise coincides with the conclusion.
      exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66769863109874523539757661593 : ((True → (p4 ∧ ((((p1 ∨ False) ∧ p3) ∧ p3) ∨ (p3 → (((((False ∨ p2) → p3) ∧ True) → ((False → p3) ∨ p1)) ∧ (p2 ∨ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37099389473417821270995875601 : ((((((p1 ∨ ((((((False ∧ p1) → p1) ∧ p1) ∨ p2) ∧ ((((p3 ∧ False) → p3) → True) → p3)) → p5)) ∧ p1) → p2) ∧ p2) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166666156596918827267326133722 : ((p2 → (((((((p3 ∧ p2) ∧ ((p3 ∨ p4) → True)) ∨ False) ∧ False) → p5) → p3) ∧ False)) ∨ ((True ∧ p1) ∨ (p5 → (p1 → (p5 ∧ p5))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350220506777230615136165034350 : (p4 → (((False ∧ p3) ∨ (True → (((p4 → True) → (((p3 → p1) → ((p5 ∧ p5) ∧ True)) → p1)) ∨ ((p4 ∨ p3) ∨ (p2 ∨ p5))))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714666095548990441864524160791 : (((((True ∨ p2) → (p3 ∨ (p4 → p1))) → (p4 ∨ (((False ∨ (((p4 → p5) ∧ p2) → (p3 ∨ ((p1 ∨ p2) ∨ p1)))) ∧ True) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664252241650387745058754282904 : ((((p1 ∨ ((p2 → ((p3 → True) → p2)) ∧ (True ∧ ((((False ∧ p4) ∨ (p2 → (p3 → p3))) ∨ p3) → (p5 ∨ True))))) → (p5 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318866521398708851939037232826 : (p4 ∨ ((((((p3 ∧ (False ∧ p2)) ∨ (p4 ∧ (p3 ∧ (p1 ∨ (p3 ∧ (p4 ∨ p1)))))) ∨ p4) → p4) → (p4 ∧ p5)) ∨ (True ∨ (p2 ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165041079855963445355230306556 : ((((p3 → True) ∧ (p1 ∧ (p3 → ((True ∨ p4) → ((p3 ∨ (p5 ∧ True)) ∧ p2))))) → p5) ∨ (((p1 ∨ True) → (p2 → (p1 ∨ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214822237081720315914860925015 : (((p4 ∨ False) ∨ (False ∨ p2)) ∨ ((p4 → ((True → ((p1 → p4) → p2)) → ((p5 ∨ p4) → ((p3 ∨ p4) → p2)))) ∧ (p1 → (p1 ∧ True)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h6 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h8 := h2 h7
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : (p1 → p4) := by
        -- Implications on the right can always be decomposed.
        intro h10
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h11 := h8 h9
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h14 := h2 h13
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h15 : (p1 → p4) := by
        -- Implications on the right can always be decomposed.
        intro h16
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h17 := h14 h15
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h19 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h20 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h21 := h2 h20
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h22 : (p1 → p4) := by
        -- Implications on the right can always be decomposed.
        intro h23
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h24 := h21 h22
      -- One of the premise coincides with the conclusion.
      exact h24
    case inr h25 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h26 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h27 := h2 h26
      -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
      have h28 : (p1 → p4) := by
        -- Implications on the right can always be decomposed.
        intro h29
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h27, we can now drive its conclusion.
      let h30 := h27 h28
      -- One of the premise coincides with the conclusion.
      exact h30
  -- Implications on the right can always be decomposed.
  intro h31
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h31
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43593291540618118332699553062 : (((((False ∧ (True ∨ (p4 ∧ (((False ∨ (p2 ∨ True)) ∧ (p4 ∧ (((p3 → p1) → p3) ∧ p2))) ∨ (p5 ∧ True))))) ∨ p4) → p3) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118906853749230027533102568452 : ((True → (p1 → ((p3 ∨ (((p5 ∨ p3) ∧ ((False ∧ p3) ∨ (True ∨ ((False → False) ∧ (False ∧ p1))))) ∧ (p1 → p2))) ∧ p1))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49539849872228257914023815037 : ((((((((True ∨ ((p1 ∧ p3) → p2)) → p1) → p5) → True) ∧ (((p2 → True) → p5) ∧ p1)) → (False ∧ p5)) → (True → (p5 → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238746016312760064430771946983 : ((p1 ∨ True) ∧ (((p4 ∧ True) ∨ ((p2 → (p5 → p2)) ∨ (p5 → (p1 ∧ p4)))) → ((p4 ∧ ((((True → p5) ∨ True) → False) ∧ True)) → p2))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h10 : ((True → p5) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h11 := h5 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h14 : ((True → p5) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h15 := h5 h14
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h17 : ((True → p5) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h18 := h5 h17
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53510588974799161974328099281 : (((p5 ∨ (((False ∨ p2) → (p1 ∧ (True → (True ∨ True)))) → p3)) → (((p2 ∨ (((p1 → (p2 ∧ False)) → p2) ∧ p5)) ∨ p2) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148305791572248589682783648291 : ((((p2 ∧ p2) ∨ (p3 → ((p5 ∨ ((p1 ∨ p4) ∨ ((True ∨ False) ∧ p1))) ∨ False))) → (p4 ∧ (p2 → p3))) ∨ (p1 → ((p3 → p4) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51337172996617771452547594166 : (((p3 → ((p2 ∨ ((p1 ∧ p3) ∧ p4)) ∧ (p3 → ((p3 ∧ (p4 → (p2 ∧ p1))) ∧ p4)))) ∨ (False → ((True ∨ p2) ∧ (False ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225371765572807873260859007992 : (((p2 ∨ False) ∧ p1) ∨ ((True ∧ (True → (True → (((p2 → ((p3 ∨ p3) ∧ (p1 ∨ p2))) ∨ (p5 ∧ (p3 → p1))) ∨ p2)))) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190812593570382741973649788578 : (((True ∧ (p3 ∧ (True ∧ (p1 ∨ p1)))) ∨ (p3 ∧ p3)) ∨ (True ∧ (((p1 → (((p4 ∨ True) ∨ p2) → (True ∨ p4))) ∨ (True → p1)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684785765084919154549122846714 : (((((p5 ∨ p3) ∨ (p4 ∧ (((True → p5) → (True → (True ∧ (True ∨ (p2 ∧ True))))) ∨ p3))) ∨ (p1 ∨ ((p3 ∨ (False → p4)) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42968246243699564819050848551 : (((p5 → ((p2 ∧ (False → ((p3 ∧ True) ∨ ((True ∧ ((p2 ∨ False) ∨ p4)) ∨ ((p4 ∧ ((p3 → p1) → p3)) → p3))))) → False)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761083563447183345219807892985 : (((p2 ∧ (p2 → ((p2 ∧ (True ∧ (p5 → ((p5 ∧ ((p1 ∧ p3) ∨ (p4 ∧ p3))) ∨ (False ∧ (p3 → p2)))))) ∧ (True → (p5 ∨ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66168270574369242310855229235 : ((p5 ∨ ((True ∧ (((p4 → p1) ∨ p5) → ((p4 ∧ (p1 ∨ p4)) ∧ (((p5 ∨ p5) ∨ False) → (p4 ∨ p3))))) ∨ (False ∨ (p4 → True)))) ∨ p3) := by
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
theorem thm_5_vars_67899290551664403679100473682 : ((p2 → (((p2 ∧ (p1 ∨ p2)) ∧ ((p5 → (p1 ∨ ((True ∨ p2) ∨ (p2 ∧ p3)))) → p3)) → (False ∨ (((True → p3) ∨ p2) ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300228482211380189392229986672 : (False ∨ ((((p2 → True) ∧ (p4 ∨ (False ∨ (True ∨ p2)))) ∧ ((False → p4) → (((p4 ∧ False) ∧ False) ∧ ((p5 ∧ p5) ∨ p5)))) → (p3 ∨ p3))) := by
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
  cases h5
  case inl h6 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : (False → p4) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h7
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h16 : (False → p4) := by
          -- Implications on the right can always be decomposed.
          intro h17
          -- False on the left can always be used.
          apply False.elim h17
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h18 := h3 h16
        -- We need to get the left conjuct of h18 based on <expert-advice>.
        let h19 := h18.left
        -- We need to get the right conjuct of h19 based on <expert-advice>.
        let h20 := h19.right
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h22 : (False → p4) := by
          -- Implications on the right can always be decomposed.
          intro h23
          -- False on the left can always be used.
          apply False.elim h23
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h24 := h3 h22
        -- We need to get the left conjuct of h24 based on <expert-advice>.
        let h25 := h24.left
        -- We need to get the right conjuct of h25 based on <expert-advice>.
        let h26 := h25.right
        -- False on the left can always be used.
        apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180218517289476235762914084363 : ((((p3 ∧ p4) → (p2 ∧ (p4 ∨ ((p5 ∨ p4) → (True → p3))))) → p3) → (((((p1 ∧ p5) ∨ (p4 ∨ (p3 → p4))) ∨ True) ∧ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626128909924786098967095366113 : ((((p3 → ((((p1 ∨ p1) ∨ ((((p4 ∧ (p4 ∨ p1)) → True) ∨ True) → (False ∨ (p1 → p5)))) ∨ (p2 ∨ (False → True))) ∧ True)) ∨ p1) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321133443147458552479058756649 : (p4 ∨ (p2 ∨ (((p3 ∨ p4) → (p4 → (p5 ∧ (True ∨ (p1 ∨ (p4 → p2)))))) → ((p5 ∨ (p2 ∧ p2)) ∨ ((True ∨ (p2 → p2)) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610335678533963154952421648532 : ((((((((p1 ∨ ((p4 ∨ (p2 ∧ ((p2 ∨ ((p2 → p1) ∧ p1)) → p5))) ∨ ((p5 ∧ True) ∧ p2))) ∨ p4) ∧ p4) → p4) → p5) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_669607926823096508412399014466 : (((((((((((p4 ∧ p2) ∧ (p4 → (p5 ∧ p3))) ∨ p5) → False) ∧ False) ∨ p4) ∨ True) ∨ ((p2 → p5) ∨ p3)) ∨ (p1 → (p2 ∨ p3))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219750394800074039208344862888 : ((p2 → ((True ∨ p1) ∧ False)) → ((p3 ∨ (p1 ∧ False)) → (p1 ∨ (((p4 → ((True ∨ p1) ∨ ((p3 ∧ False) ∧ (True → True)))) → p2) ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259056485325195876560237681985 : ((True → p4) → (p1 → ((((p2 → p3) → (p2 → ((False ∧ ((p1 ∧ p1) ∨ (p3 ∨ (p4 → (p3 ∨ False))))) ∨ p5))) ∨ p2) ∨ (True ∧ p4)))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_812210337110141747263157680778 : ((((((((((True → ((p1 ∧ (((p3 ∧ p2) → True) ∨ p1)) ∧ (p5 ∨ p4))) → p5) ∨ (p5 → p4)) ∨ p1) → p1) → False) ∧ p1) ∧ p1) → p5) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (((((True → ((p1 ∧ (((p3 ∧ p2) → True) ∨ p1)) ∧ (p5 ∨ p4))) → p5) ∨ (p5 → p4)) ∨ p1) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
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
      exact h11
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h12 := h4 h6
  -- False on the left can always be used.
  apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241323274637712682190877452465 : ((False → True) ∧ (p1 → (((((((True ∨ (p4 → (True ∧ p1))) ∧ (p5 → p4)) ∨ p2) ∨ p4) → p3) ∨ ((p4 → p1) ∧ (p3 ∧ p3))) ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300153322617431771107778285269 : (False ∨ ((p3 ∨ (p5 → (((p4 ∨ True) ∧ p5) → ((False ∨ p2) ∨ ((p4 → (p5 ∧ (((False ∧ p2) ∧ p4) ∨ True))) ∨ p4))))) ∨ (p5 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h3
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694192886409069961035770475709 : (((((p2 → (p5 ∨ (p1 ∨ (True ∧ True)))) → (p5 ∨ (p2 ∨ (p1 ∧ p4)))) ∨ (False → ((p1 → (p4 ∨ p1)) ∧ ((True ∨ p5) ∨ p2)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117564174553887138855793749834 : ((p2 ∧ (((p2 ∨ (p5 ∨ p3)) ∧ p1) ∧ (False ∨ (((p1 → (p1 ∧ ((p4 → p3) ∧ (p4 → p1)))) ∨ (True → p5)) → p1)))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59680039156546450977088176871 : (((True ∧ p3) → (False ∧ (((((p5 → p2) ∨ p2) ∨ (p3 ∨ ((p3 ∨ p1) → True))) ∨ (False ∧ p1)) → ((p3 ∧ p1) → (p1 → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315009109012579933547267585480 : (p3 ∨ (((p1 ∧ (False ∧ (p1 ∨ (True ∨ p5)))) ∨ p5) ∨ (((p4 ∧ (True ∨ ((p1 → (True ∨ (False → p2))) → (False ∨ p2)))) → p4) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606603120258931466208810117195 : (((((((False → p2) → ((p1 ∧ (p2 → (p3 ∨ False))) ∧ ((p1 → p5) ∨ ((False ∨ p2) ∧ (p4 ∧ (p4 ∧ p4)))))) → False) ∧ p5) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43682874479635054656732126730 : (((((p1 → ((p2 ∧ ((((p1 ∨ False) ∧ p3) → p1) ∨ p5)) ∨ True)) → (((p1 ∧ p2) ∨ p4) ∨ ((p1 → p2) ∧ False))) → False) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307833254701580394541805291493 : (p1 ∨ (p4 → (p2 ∨ (p5 ∨ ((p4 → (False ∧ ((((True ∧ (p1 ∧ p3)) → p4) ∨ (True ∧ p1)) ∧ (((p2 ∧ True) ∨ True) ∨ p4)))) ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113140185122890070186846056700 : (((p2 → (p3 ∧ (p3 ∨ ((((((p3 → True) ∧ p3) ∧ (p1 ∧ (p3 ∧ ((True ∨ p1) ∨ p2)))) ∨ p5) ∧ True) ∨ p2)))) → p5) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113545472613689645787405744456 : ((((True ∧ (p3 ∨ p5)) ∧ (p4 ∨ (p3 ∨ ((p2 → (p5 ∧ ((True ∨ ((True ∨ True) ∧ p1)) → True))) → p5)))) ∨ (p5 → p5)) ∨ (False ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_443444673477141893966882156670 : (((((((False ∧ True) → (p4 ∧ (p1 ∨ (p4 ∨ p4)))) → True) → (((True → p5) → ((p2 → p5) ∨ False)) → p3)) ∨ (True ∧ (p2 → p2))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173234042121504713818822158186 : ((True → ((((p5 ∧ True) ∧ p4) → (p1 ∨ (p2 ∨ (False ∨ p2)))) ∧ (False ∧ p4))) ∨ (True ∨ ((p3 ∨ False) → (((False ∨ p5) ∧ True) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67853241024101239268394650755 : ((p2 → ((((False ∧ (p5 ∨ p3)) → p3) ∨ ((((False → (True ∧ p1)) ∨ p5) ∨ (p3 ∨ p2)) ∧ ((p5 → p5) ∧ p4))) → (p1 → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198431479162734923539098206393 : ((p4 ∧ (p1 ∨ (((p2 ∨ p3) ∨ p2) ∨ p3))) ∨ (p5 ∨ (p4 → ((False ∧ (p5 ∧ p2)) → (p1 ∨ (p4 → (((p4 → p3) ∧ True) ∧ p4))))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223479385939055462628794326049 : ((False ∨ (True ∨ p4)) ∧ (((p4 ∨ (p1 ∧ True)) ∨ False) ∨ ((p3 ∨ (p5 ∨ (True → (((True ∨ p1) ∨ (False → False)) ∨ p2)))) ∨ (False ∧ True)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201994596499420967285184185646 : (((p3 → (p3 ∨ (p1 ∨ p5))) ∨ True) ∧ ((((p4 ∧ (p2 ∧ p1)) ∧ (p3 → (p3 ∧ p5))) ∨ (p4 ∨ True)) ∧ ((True ∨ (False ∨ True)) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709077260099989765338266545941 : ((((((p3 → p5) ∨ p5) ∨ ((p3 ∧ p2) → False)) → ((True → False) → ((False ∨ p3) ∧ (p5 → ((False ∨ (True ∧ False)) → (p1 ∨ p4)))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h5 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h6 := h2 h5
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h9 := h2 h8
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- False on the left can always be used.
    apply False.elim h12
  -- Implications on the right can always be decomposed.
  intro h13
  -- Implications on the right can always be decomposed.
  intro h14
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h15 =>
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- False on the left can always be used.
    apply False.elim h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754092536350165797524106711778 : (((False ∧ (((p3 → p4) ∧ False) ∧ ((((p4 → p3) ∨ (((p1 ∨ True) ∨ p4) ∨ p2)) ∧ p5) ∧ ((True → p1) ∨ (p1 ∧ (p5 → p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38646591128458272745110974992 : ((((((p3 → (p2 → (p5 ∧ p3))) ∧ True) → p4) → (p4 → (((True ∨ ((p2 ∨ (p1 ∨ p1)) → p3)) → (False ∧ p4)) ∧ p4))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_442836497349667256839835009801 : (((((p3 ∨ ((((((False ∧ True) ∧ ((True ∨ p5) → p3)) → True) → False) → (p5 ∨ p2)) → p4)) ∧ (p1 ∧ p1)) ∨ ((p1 ∧ p4) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309402741642399031345166895557 : (p2 ∨ ((True → ((((((True → ((p3 → (p5 → False)) ∨ True)) ∧ (p3 ∧ p4)) → (True ∨ p1)) → (p4 ∧ p2)) ∨ p3) ∨ True)) ∨ (True → p4))) := by
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
theorem thm_5_vars_212206136508986066315664717719 : ((True ∨ (p4 → (p2 → p2))) ∧ (((p2 ∨ (((False ∧ True) → p1) → (((False → (p3 → (p3 ∧ p5))) ∧ p1) ∨ False))) ∧ p5) ∨ (p4 → True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



