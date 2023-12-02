variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175421474793515067318990256547 : ((False → (False ∨ (((p1 ∨ p1) ∧ p1) ∨ (p3 → ((p1 → (True ∨ p4)) ∨ True))))) → ((p2 → (p4 ∨ p5)) ∨ (True → ((p2 → True) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_823706267733278661193556481023 : (((((((p2 → False) ∨ False) ∨ False) ∧ (((False ∨ p2) → (p5 → (((p2 ∨ p2) → ((p4 ∨ p5) ∧ p2)) ∧ p4))) → (True ∧ p5))) ∧ p2) → False) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h8 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h9 := h7 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356740452481766038013894943110 : (p5 → ((p4 ∧ (p2 ∨ ((p1 ∧ p4) ∨ p4))) ∨ ((p2 ∨ p2) ∨ (((p2 ∧ (p4 ∧ p2)) ∨ (((p2 ∧ True) → False) → p5)) ∨ (p1 → p5))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157374943301369758239457388336 : (((p5 → (((p1 → p4) ∧ False) → (p1 → (p2 ∨ ((p3 ∨ p3) ∨ (True ∧ (p3 ∨ p3))))))) → p5) ∨ (False → ((p5 ∧ p5) → (p5 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321230884955192535289152273619 : (p4 ∨ (p4 ∨ ((((((p3 ∧ ((p5 ∨ True) → (False ∨ p4))) → ((p3 ∧ False) ∨ (((p5 → False) ∨ p3) ∧ p4))) → False) ∨ p3) ∨ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200240301991520144193722417408 : ((((False ∧ p3) → p4) → ((p5 ∧ p1) ∧ p3)) → (((((p2 → p3) ∧ p3) ∨ (((True → p2) → (False ∨ p1)) → (p2 ∨ p3))) ∨ p1) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∧ p3) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45696842830993217991009981546 : (((p5 ∨ (p4 → ((((p4 ∨ (p1 ∨ ((False ∨ p1) ∧ p3))) → p2) ∧ (p2 ∧ False)) ∨ (p2 ∧ (((p3 → True) ∨ p2) → p1))))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134858745409132059980150430252 : (((True → ((False ∨ (True ∧ p3)) ∧ (((((p2 ∨ p3) ∨ p2) → True) ∧ False) ∧ ((True ∧ (p4 → True)) ∧ p4)))) → p4) ∨ ((False ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47621277734670247259596553444 : (((p5 → ((((False ∨ p1) ∨ (False ∧ p4)) ∧ False) ∨ (p5 ∨ (p4 ∧ (p1 → ((((p4 → True) → True) → p4) → p2)))))) ∨ (p5 ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625039777854815638029742072059 : ((((True → ((p5 ∨ ((p1 ∨ (p3 → ((True → (((False ∨ ((p4 ∧ (True ∨ True)) ∧ p3)) ∧ p3) → p1)) → p5))) ∨ p3)) ∧ p2)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185281184102008904112948225149 : ((p2 ∧ ((p5 ∧ ((p2 ∧ (p1 ∨ p1)) ∨ (p4 ∨ True))) ∨ p5)) ∨ ((((((p5 → True) ∨ p5) → p2) ∧ (p1 ∧ p1)) ∨ (p4 ∨ True)) ∨ p3)) := by
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
theorem thm_5_vars_167347635574654867298906270060 : ((((True ∧ (((p2 → p5) → (p2 ∧ True)) ∧ (True ∧ True))) → ((p2 ∧ p1) → p1)) → False) → ((False ∨ ((p2 ∧ (p4 ∧ p1)) ∨ p3)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∧ (((p2 → p5) → (p2 ∧ True)) ∧ (True ∧ True))) → ((p2 ∧ p1) → p1)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h2
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159832698165291773874271000730 : (((p4 ∨ (p5 ∨ (((False → False) ∧ p3) → (p4 → (True → (((p2 → False) ∨ p5) ∨ p2)))))) ∨ p5) → (True → ((p3 ∨ p5) → (p2 ∨ True)))) := by
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
    cases h1
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
    cases h1
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
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
theorem thm_5_vars_138055426180718065661764140633 : ((True → (False ∧ (((True ∧ (p4 ∧ True)) ∨ (p3 → (p2 ∨ False))) ∧ ((p5 → (p3 → (p4 ∧ p4))) ∧ (p4 ∧ False))))) ∨ (p5 → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46000138266140847685811194371 : (((((((True ∧ ((False ∧ (p3 → p5)) ∧ True)) → p1) ∨ (p5 → ((p4 ∨ (False → p3)) → p5))) → (False ∨ p3)) ∧ p5) ∧ (True ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199692815144692879607951620069 : (((True ∧ ((False → (p2 ∧ True)) → p1)) → True) → (True ∧ (((p4 ∧ (p3 ∨ ((False ∧ False) ∨ p5))) ∨ True) ∨ ((p5 ∨ (p2 ∨ p2)) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_329649890543698388585300471481 : (True → ((p3 ∧ p3) → ((((((False ∧ (True ∨ p5)) ∨ False) → p4) → p4) ∧ ((p5 ∨ p4) ∨ (((p1 ∨ p4) → True) ∧ p2))) ∨ (p1 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204401720736105311406119226261 : (((p1 → (True ∨ (False → p2))) ∧ p2) ∨ (((((p3 ∨ True) ∨ (p5 → (p4 ∧ False))) ∧ p2) ∧ (p3 ∨ p3)) → ((p3 → False) → (p1 ∧ p5)))) := by
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
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h9 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h10 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h11 := h2 h10
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h13 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h14 := h2 h13
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h16 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h17 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h16
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h18 := h2 h17
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h20 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h19
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h21 := h2 h20
        -- False on the left can always be used.
        apply False.elim h21
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h23 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h24 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h23
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h25 := h2 h24
      -- False on the left can always be used.
      apply False.elim h25
    case inr h26 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h27 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h26
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h28 := h2 h27
      -- False on the left can always be used.
      apply False.elim h28
  -- Conjunctions on the left can always be decomposed.
  let h29 := h1.left
  let h30 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h31 := h29.left
  let h32 := h29.right
  -- Disjunctions on the left can always be decomposed.
  cases h31
  case inl h33 =>
    -- Disjunctions on the left can always be decomposed.
    cases h33
    case inl h34 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h35 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h36 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h35
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h37 := h2 h36
        -- False on the left can always be used.
        apply False.elim h37
      case inr h38 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h39 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h38
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h40 := h2 h39
        -- False on the left can always be used.
        apply False.elim h40
    case inr h41 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h42 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h43 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h42
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h44 := h2 h43
        -- False on the left can always be used.
        apply False.elim h44
      case inr h45 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h46 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h45
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h47 := h2 h46
        -- False on the left can always be used.
        apply False.elim h47
  case inr h48 =>
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h49 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h50 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h49
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h51 := h2 h50
      -- False on the left can always be used.
      apply False.elim h51
    case inr h52 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h53 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h52
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h54 := h2 h53
      -- False on the left can always be used.
      apply False.elim h54



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336104364444619876099796078249 : (p1 → (((p5 → (((p2 → p5) → (True → (((p4 ∨ (p2 → p2)) → (((p5 → p4) ∨ (p5 → p5)) ∧ True)) ∨ p5))) ∧ False)) ∧ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345479470329203903255759966087 : (p3 → ((((p5 → p3) ∨ (p1 ∧ ((p5 ∧ p5) ∨ (((p1 ∨ p5) ∧ p2) ∨ (p5 ∧ ((True → p3) ∧ p5)))))) → (p4 ∨ (p4 → True))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
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
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h16 =>
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
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h25
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227818061677786796086335910662 : ((p2 ∧ (p1 ∧ p1)) ∨ ((True → (p5 ∨ p5)) ∨ (((((((p4 ∧ p3) ∨ p3) → p5) → (p1 ∧ (p2 → p5))) ∧ p5) → p1) ∨ (True → True)))) := by
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
theorem thm_5_vars_962419678718480971845345114507 : ((((True → False) ∧ (True ∧ ((p3 ∧ p5) → ((((((((p4 → (True ∨ p5)) ∧ p2) ∨ False) ∨ p5) ∨ p2) ∧ False) ∧ False) → (p5 → False))))) → p4) ∧ True) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110720332776112265959408138215 : (((((((p1 → ((p4 ∧ ((p3 ∨ ((True → p3) → False)) ∧ p4)) ∧ p2)) ∧ p1) ∧ (True ∧ p1)) ∨ (p5 → p3)) ∧ p5) ∧ p5) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139708123403465008786131049585 : ((((p1 ∨ p2) ∨ ((p4 → ((((((p2 ∧ ((p2 → p2) → p1)) ∨ p1) ∨ p2) ∨ p4) ∧ p4) → p2)) → p2)) → p5) → (p5 → (p5 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167975417321089397491612359139 : ((((p4 ∨ (False → (p3 ∨ p2))) ∧ p2) ∧ (p3 ∨ ((p2 ∨ True) → (p3 ∧ (p5 ∧ p3))))) → ((p3 ∧ p4) ∨ (p4 ∨ (True ∧ (False ∨ p3))))) := by
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
    cases h3
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : (p2 ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h13 := h11 h12
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205868119023887307809524595787 : ((True ∧ (((p2 ∨ p1) ∧ p3) ∧ p4)) ∨ ((p2 ∨ p5) ∨ (((True ∧ False) → ((True ∧ (p2 ∧ (p1 → True))) ∧ (p4 → p1))) ∨ (p3 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652168241033466554304990692582 : ((((p1 ∧ (p1 → (((((p4 → p2) ∨ ((True → False) ∨ p2)) → p1) → ((p1 → ((p5 → p3) ∨ False)) ∧ p4)) ∨ p1))) ∧ (p3 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63428230327168508226766166469 : ((p5 ∧ (p1 → ((((((p2 ∨ p5) → p4) ∨ p1) → (((False ∧ (p3 ∧ ((p4 → True) → (p3 ∨ False)))) ∨ p2) ∧ False)) ∨ False) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161805598863480730207555291379 : ((p5 ∨ (((p5 ∧ (True ∨ (True → p4))) ∨ p5) ∧ (((False ∧ p2) → (p5 → (p5 ∨ False))) → False))) → (p4 → ((p3 ∧ p3) ∨ (p2 ∨ p5)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
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
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198006011095904993489348971834 : (((p1 → True) ∧ (False ∧ (p3 ∧ (p4 → p5)))) ∨ ((((False → ((p2 ∨ p1) → p1)) → p5) ∧ p4) ∨ (p5 ∨ ((p2 ∧ False) → (True → p3))))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624425790672966041595478173671 : ((((p3 ∨ (p2 ∨ (((p2 → ((p1 ∧ ((True ∨ p1) → False)) ∧ (p2 ∨ (p2 → False)))) ∨ (False → (p4 → (True ∨ p5)))) ∨ p5))) ∨ p4) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319458753732267980597801056290 : (p4 ∨ (((p2 ∨ ((p5 ∧ True) → (True → p4))) → ((p4 → p3) → p2)) ∨ ((False ∧ p5) → ((((p2 ∧ True) ∨ True) ∨ p2) ∨ (p4 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_66712202740531377632745969701 : ((True → ((p4 ∨ p4) ∧ (p4 → (p4 ∧ (((((p1 ∨ (p3 ∨ (((False ∨ (p2 ∧ p5)) → p5) ∨ p4))) ∧ True) → p2) ∧ p3) → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252302201307552827057720639801 : ((p4 → p5) ∨ ((p3 → p2) → ((p5 ∧ (False ∧ (p3 → False))) ∨ (((p5 → p4) → True) ∨ (((False ∧ (p3 ∨ p3)) ∧ (True → p4)) ∧ p2))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604841129323256030060815766219 : ((((p1 → ((((p5 ∧ (((p5 ∨ p4) → (p3 ∧ (p2 ∨ (p4 ∨ p3)))) → (p4 ∧ p2))) ∨ False) ∨ p2) ∨ ((p2 → p5) → p1))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251890580549329840729672491503 : ((p3 → p5) ∨ (p1 → (((p5 → (p2 ∨ (p2 ∨ p3))) → True) → ((p5 ∨ p1) ∧ ((((p5 ∧ p4) ∨ ((True ∧ p1) ∨ p1)) ∨ p2) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737224782211632117983252401015 : ((((p4 → True) ∧ (((p4 → False) ∨ p4) → (((p3 ∨ True) → ((p2 → p1) ∨ (((p1 ∨ ((True ∧ p5) ∨ p5)) → p4) ∧ p3))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784336021317255832289147175949 : (((p3 ∨ (p2 ∧ (((((p5 ∨ p3) ∧ (((((p4 → (p4 ∧ p2)) ∨ p1) ∧ p1) ∨ (p3 → False)) ∧ False)) ∨ p1) ∧ False) ∨ (p3 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260102986464997491036668329260 : ((p2 → p1) → ((False ∨ (p3 ∧ (((p2 → p3) ∧ ((p1 ∨ (p1 ∧ p3)) → (p2 ∨ (False → (p1 ∨ ((True → p5) → p1)))))) ∨ p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724104544931449624320049397243 : ((((p2 ∧ (p1 ∧ p2)) ∧ (((p2 ∨ (p5 ∨ ((((p1 ∧ True) ∧ p2) → (p1 → (p4 ∨ (p3 ∧ True)))) ∧ (p3 ∧ False)))) ∧ True) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353717172012682242047845975603 : (p4 → (True → ((True ∧ ((False ∧ ((True ∧ p3) ∨ ((p2 → (p4 → (p5 ∨ False))) ∧ p3))) ∨ ((True ∨ p4) ∧ (p4 → (True ∧ p4))))) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302629984126696475114429770970 : (False ∨ (p2 ∨ ((((p4 ∨ (p3 ∧ p1)) ∨ (p3 ∧ (((p1 ∨ p1) ∧ (((p2 → False) ∨ p1) ∨ p4)) ∨ p5))) ∨ (True ∨ p5)) ∨ (p1 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_764935516807911774593465125145 : (((p4 ∧ (((p1 → p2) ∧ (((p3 ∧ (p2 ∨ p3)) → ((p5 → ((p3 ∨ p4) ∧ p2)) ∧ (True → ((p2 → False) ∧ p3)))) ∨ p4)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117582692979292750497653501357 : ((p2 ∧ (True ∧ (((p3 ∨ p3) ∨ (p2 ∧ (((p3 ∧ (p1 → p5)) ∧ p1) ∧ (p5 ∧ (p4 ∧ ((p5 ∧ p3) ∨ p1)))))) ∧ True))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137450390634753771825157589164 : ((p4 ∧ ((p4 ∨ ((p2 → p5) ∧ True)) → (p4 ∨ (p5 ∨ (True → ((p2 ∨ (p3 ∨ (p3 ∧ p1))) ∨ (True ∧ p3))))))) ∨ (p1 ∨ (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750983916547639887147496307532 : (((True ∧ ((p2 ∧ ((p5 ∧ (p3 ∧ p1)) ∧ p3)) ∨ (((False → (p4 → ((True ∨ p4) ∨ False))) ∧ ((p4 → (p5 ∨ p4)) → p2)) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140053039378517309675179370041 : (((((True → (True ∧ (False ∧ True))) ∨ (False ∧ p1)) ∧ ((p2 → ((False → (p1 ∨ p4)) ∨ p4)) → p1)) ∨ (p2 ∨ False)) → (False ∨ (p1 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h7 := h5 h6
      -- We need to get the right conjuct of h7 based on <expert-advice>.
      let h8 := h7.right
      -- We need to get the left conjuct of h8 based on <expert-advice>.
      let h9 := h8.left
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204257078837809284947195049136 : ((((p1 ∧ p4) ∨ (p3 ∨ False)) ∧ p4) ∨ ((p3 ∨ False) ∨ (p5 ∨ (((p1 ∨ p1) ∨ (((False ∨ False) → (p2 → p4)) → (p2 ∨ p4))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47313246618348009089433132604 : ((((False ∨ (p1 ∧ p2)) ∨ (True → (((p5 ∨ ((((p3 ∨ (p4 ∧ True)) ∧ p1) → p5) ∨ False)) ∨ False) ∨ (True ∨ False)))) ∨ (p2 → p4)) ∨ p1) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1456247716940403613778118682 : (((((((p3 → p2) ∨ p5) ∨ ((False → p2) ∨ ((p4 ∧ (True ∧ (True ∧ p2))) ∨ (p5 → p5)))) → p4) ∨ p5) ∧ p5) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157643949082553941161000666644 : (((True → (((p2 → (p3 → p3)) ∧ (p5 ∨ p5)) ∧ ((p2 ∧ True) ∨ p5))) ∧ ((p3 ∨ p3) ∨ p4)) ∨ (p5 → ((p2 ∨ (p5 ∧ p3)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51612564869912088783666961882 : ((((((p2 ∧ (p1 → ((p1 ∨ p2) ∨ ((True ∧ p4) → p1)))) ∨ p4) → p5) ∧ p4) ∧ (p2 ∨ ((False ∨ (p3 ∨ p3)) ∧ (p3 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134221283074909787810490202565 : ((((((p2 ∧ (p1 → True)) → p5) ∧ p1) ∨ ((p3 ∧ p3) ∨ ((False ∧ (p1 ∧ p1)) → ((p1 ∧ p3) ∨ p4)))) ∨ p4) ∨ ((True ∧ p1) ∨ p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197885943514463960445050312662 : ((((p1 ∧ p1) → True) → (False ∧ (p4 ∧ True))) ∨ ((((p5 ∧ (p5 → (False → p1))) ∧ (True ∧ (p5 → ((p5 ∧ True) → False)))) ∧ p3) → p3)) := by
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
  let h8 := h5.left
  let h9 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165528849704784723138730500329 : (((p5 ∧ (True ∨ (p1 ∨ ((p3 → p5) ∨ (p5 ∨ p1))))) → (p3 ∨ (False ∧ (p3 ∨ True)))) ∨ (((p3 ∨ True) ∧ (True ∨ p1)) ∨ (True ∧ p3))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586032788784660730395257076534 : ((((((p5 ∨ ((False ∨ p1) ∧ (False ∧ ((((False ∧ True) → (p3 → p3)) → False) ∨ (p4 ∧ p2))))) ∨ (True ∨ (p4 ∨ p3))) ∧ p1) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64120897423930366693401242193 : ((False ∨ (((p2 ∧ (p1 ∨ p5)) → (False ∧ p5)) → ((((p4 ∧ False) ∧ False) ∧ (p2 → (True → (True ∧ (False ∨ (p1 ∧ True)))))) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51379310314937111004187847293 : (((((p3 ∧ ((False ∨ p2) ∧ (p2 ∨ ((p2 ∧ (p1 ∨ p2)) ∨ p1)))) ∧ (p4 ∧ p2)) ∨ False) → ((True → p4) → ((False ∨ False) ∨ p2))) ∨ p2) := by
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
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h5.left
        let h14 := h5.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- Conjunctions on the left can always be decomposed.
            let h20 := h5.left
            let h21 := h5.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h21
          case inr h22 =>
            -- Conjunctions on the left can always be decomposed.
            let h23 := h5.left
            let h24 := h5.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h24
        case inr h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h5.left
          let h27 := h5.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h27
  case inr h28 =>
    -- False on the left can always be used.
    apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10622912089590774967923450549 : (((p5 → ((p4 → False) ∧ (((p1 ∨ ((False → (((p2 → p5) ∧ False) → ((p2 → (p2 ∨ p5)) ∧ p4))) ∧ p3)) → p5) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87306241720459156287714848079 : (((((p3 → p4) → False) ∧ (p3 → p4)) ∧ (((p2 → (p4 → p3)) ∧ ((((p4 → p1) ∨ (False → p1)) ∨ p3) ∨ (p4 → True))) ∨ p2)) → p3) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h12 : (p3 → p4) := by
            -- Implications on the right can always be decomposed.
            intro h13
            -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
            have h14 : p3 := by
              -- One of the premise coincides with the conclusion.
              exact h13
            -- We have shown the premise of h5, we can now drive its conclusion.
            let h15 := h5 h14
            -- One of the premise coincides with the conclusion.
            exact h15
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h16 := h4 h12
          -- False on the left can always be used.
          apply False.elim h16
        case inr h17 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h18 : (p3 → p4) := by
            -- Implications on the right can always be decomposed.
            intro h19
            -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
            have h20 : p3 := by
              -- One of the premise coincides with the conclusion.
              exact h19
            -- We have shown the premise of h5, we can now drive its conclusion.
            let h21 := h5 h20
            -- One of the premise coincides with the conclusion.
            exact h21
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h22 := h4 h18
          -- False on the left can always be used.
          apply False.elim h22
      case inr h23 =>
        -- One of the premise coincides with the conclusion.
        exact h23
    case inr h24 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h25 : (p3 → p4) := by
        -- Implications on the right can always be decomposed.
        intro h26
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h27 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h26
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h28 := h5 h27
        -- One of the premise coincides with the conclusion.
        exact h28
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h29 := h4 h25
      -- False on the left can always be used.
      apply False.elim h29
  case inr h30 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h31 : (p3 → p4) := by
      -- Implications on the right can always be decomposed.
      intro h32
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h33 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h32
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h34 := h5 h33
      -- One of the premise coincides with the conclusion.
      exact h34
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h35 := h4 h31
    -- False on the left can always be used.
    apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218157963692231383943196270049 : (((p5 → p5) ∧ (True ∧ p4)) → ((((p2 ∨ ((False ∧ (p4 ∧ ((p5 ∧ p1) ∧ (p4 ∧ (True → p5))))) ∧ (False ∧ p1))) ∨ p4) ∨ False) ∧ True)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151154126385836592123617710452 : ((((((p3 ∧ (False ∨ (p2 ∧ p4))) ∨ ((True ∨ p1) ∧ p1)) ∧ (True ∨ p1)) ∨ ((p1 ∧ p2) ∨ p3)) → False) → ((p1 ∧ p1) ∨ (p3 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((((p3 ∧ (False ∨ (p2 ∧ p4))) ∨ ((True ∨ p1) ∧ p1)) ∧ (True ∨ p1)) ∨ ((p1 ∧ p2) ∨ p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52626794721666932493883982259 : ((((p3 → (p3 → p3)) → ((((p2 → p4) → p1) ∨ True) ∧ (p3 ∨ p5))) ∨ ((True ∧ ((p4 ∨ p5) → (False → (p3 ∧ p1)))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218164406556725208499575241537 : (((True ∧ p2) ∨ (p1 ∧ p3)) → ((p5 → ((False ∨ (p1 ∧ False)) ∧ p1)) ∨ (p3 ∨ ((p1 → ((p4 → (p2 ∧ (p2 ∨ p5))) ∨ p4)) ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37937931406358862423032954907 : ((((p1 ∨ ((p4 ∧ p4) → ((p5 ∨ (p5 ∧ (((p3 → p4) → p5) ∨ p1))) → (p2 ∨ ((p3 ∧ p5) → p5))))) ∧ (p3 ∧ p1)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41827426378414919272413985623 : (((((p4 ∨ p2) → p2) ∧ ((p1 → ((p1 ∧ (((p2 ∧ (p5 ∧ p1)) ∧ p5) → p5)) → (((p4 ∨ p3) ∨ p1) ∧ p1))) → p2)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698306641596136485180476224100 : (((((p1 ∧ (((p1 ∨ False) ∧ (False → p2)) ∧ p4)) ∧ (p5 ∨ p2)) ∨ ((p4 ∧ p3) ∨ (False ∨ (p5 ∨ (True → ((p1 ∧ p3) → True)))))) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778689051186159017897028863953 : (((p1 ∨ (p3 ∨ ((((p3 → (p4 ∨ (p5 ∧ (False → True)))) ∨ ((False ∧ True) ∧ p4)) → ((p5 ∧ (p1 ∧ p1)) ∧ (p1 → p5))) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168600753737361502056257911084 : ((p3 ∧ ((p5 ∧ (p2 ∧ (p5 ∨ (True → ((True ∨ p2) ∨ ((p3 ∧ p4) ∧ p5)))))) ∧ p2)) → (p3 ∧ ((p3 → False) ∨ (True ∨ (p1 ∧ False))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h13.left
  let h15 := h13.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h17.left
  let h19 := h17.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h20 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h21 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61614026419531252571295596310 : ((p1 ∧ ((p3 → p4) ∧ (((p2 → (False → p5)) → p5) ∧ (p4 → (((p5 ∧ ((False ∧ p2) ∧ True)) → p4) → (p5 → (p3 → p1))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337406099785662842428357567907 : (p1 → (((((False → p4) → True) → (((p1 → ((p2 → (False ∧ True)) ∧ (p5 ∧ p4))) ∨ (p4 ∧ p4)) ∧ False)) ∧ True) → ((p3 → False) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((False → p4) → True) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56166369023697357853050524083 : (((p1 ∧ ((p4 ∧ p1) ∧ p3)) ∨ (((p1 ∨ False) → p1) ∧ ((((p2 → p5) ∧ p5) → (((p3 → p3) ∧ (p3 ∨ p4)) ∧ p4)) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759959716665764846260850925230 : (((p2 ∧ (((p2 ∨ p4) ∨ (True ∨ p1)) ∧ (((((p4 ∨ p2) ∨ ((False ∧ (False → ((p2 ∨ False) ∨ p2))) ∨ p2)) ∨ True) → p2) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58873495242596403480483172234 : (((False ∧ False) ∨ ((p3 → (p2 ∨ (p5 → ((p5 ∧ ((p1 → p1) ∧ ((True → p2) ∧ (False ∨ True)))) ∧ (True → p1))))) ∧ (p4 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715349709510634698763681555053 : ((((p5 → (((p3 → p4) ∧ p4) ∨ p4)) → ((p2 → (p3 ∧ (p3 → (p5 → True)))) ∨ (((True → p5) ∧ (True ∧ (True → False))) → p5))) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120047246459595324925691011586 : ((((((p2 → p2) ∧ (p2 → (False ∨ p5))) ∨ p1) ∧ ((p1 ∧ (p2 ∨ ((True ∨ p3) ∨ ((p3 ∨ p2) ∧ p1)))) ∧ p4)) ∧ p1) → (p5 ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h5.left
    let h10 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
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
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Disjunctions on the left can always be decomposed.
        cases h19
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
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h5.left
    let h25 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h24.left
    let h27 := h24.right
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h32 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h33 =>
        -- Conjunctions on the left can always be decomposed.
        let h34 := h33.left
        let h35 := h33.right
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h36 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h37 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53045331428665049727102950688 : ((((p5 ∨ False) ∧ ((((p5 ∧ p2) ∧ (p3 → False)) ∨ p1) ∨ p2)) ∧ (p1 ∨ (((p3 ∧ p5) ∨ ((p2 → False) ∧ p2)) ∨ (False ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53814478658872129629498331915 : (((((p1 ∨ p3) ∧ ((p5 → p5) ∨ p5)) ∧ (False ∧ p5)) ∨ ((True ∧ (((p4 → p3) → p3) → (p2 → p4))) ∧ ((True ∨ p1) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305325800373101956714966876892 : (p1 ∨ ((((p1 ∧ ((p5 ∨ p5) ∨ (((False → (p2 → p2)) ∧ (p2 ∨ p3)) ∨ p1))) ∧ p3) ∨ False) → ((p2 ∨ (True ∨ (p1 ∧ p2))) ∨ p1))) := by
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
        exact h5
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601035399728481165118671620074 : ((((p1 ∧ (((True ∧ (False ∧ True)) ∧ p2) ∧ ((p1 ∨ (((p4 → p3) ∨ (p1 → p1)) ∨ (p2 ∧ ((p5 ∨ p1) ∨ p4)))) ∨ False))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40621655384290350221027056391 : (((((p5 ∨ (True ∧ ((((p4 ∧ (((p4 ∨ p1) → True) ∨ p3)) → p5) → p4) ∨ (p1 ∧ ((p5 → False) → p3))))) ∨ p4) → p3) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206066434455097099582650213727 : ((p3 ∧ ((p2 → (p3 ∨ p1)) ∨ p1)) ∨ (((p2 ∨ p2) ∧ (p2 ∨ False)) ∨ (p4 → (((p3 → (p4 ∨ (p3 ∨ True))) ∨ p3) ∨ (False → p2))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787235826317882271192437487542 : (((p4 ∨ (False ∧ ((((p4 → (((p4 → p4) → (p2 ∧ (p3 ∧ p4))) ∧ ((p2 ∨ p2) ∧ p3))) ∧ p5) → p4) ∨ (p3 ∧ (p3 ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198042104149384308148474279347 : (((p2 ∧ False) ∨ ((p2 ∧ p3) ∧ (False ∨ p4))) ∨ (p2 → (((p3 ∧ (((False ∧ p5) ∨ (p5 → (p3 → (True ∨ p3)))) → p1)) → True) ∨ p3))) := by
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
theorem thm_5_vars_134182962937023562549886799587 : ((((p4 → (((p2 ∨ p2) → False) ∧ ((p1 ∧ (p1 → p3)) ∨ p5))) ∧ (False ∨ (p4 → (p3 ∨ (p1 ∨ p2))))) ∨ p1) ∨ (True ∨ (True ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48281170491147433797407453120 : (((p4 ∧ (((p3 ∨ ((p1 ∨ ((True ∨ p2) ∨ ((p2 ∨ p3) → p3))) ∨ p3)) ∧ p3) ∧ (p4 ∧ (True → (p4 → p3))))) → (False ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h5.left
    let h10 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h5.left
        let h15 := h5.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
            -- Conjunctions on the left can always be decomposed.
            let h19 := h5.left
            let h20 := h5.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h21 =>
            -- Conjunctions on the left can always be decomposed.
            let h22 := h5.left
            let h23 := h5.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h5.left
          let h26 := h5.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h5.left
      let h29 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194053734450459347312400778954 : ((p5 ∨ (p2 ∧ (((False → (False → True)) → p4) ∧ False))) → ((p2 → (((False → p1) ∧ ((p3 ∧ p1) ∨ (p5 ∨ p5))) → (p3 ∨ False))) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262132128623134383832266752277 : (True ∧ (((p5 ∨ ((((p4 → True) → ((p3 ∨ (p2 → p3)) ∧ ((p5 ∨ True) ∧ p4))) → True) → (((p1 ∧ p4) ∨ True) → p1))) ∧ p4) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166311235933940216358992493408 : ((p5 ∧ ((p5 ∨ ((p4 ∧ (p4 ∧ (p3 → (p1 ∨ ((p5 ∨ p5) ∧ False))))) ∨ p5)) ∧ p4)) ∨ ((True ∨ True) ∨ (False ∨ ((p2 ∨ p3) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633462133447895343249223903316 : ((((((((False → p4) → p4) ∨ ((p5 ∧ ((p2 ∨ False) ∧ (p3 ∨ ((p5 → True) → p1)))) ∨ False)) → (p1 → p1)) ∨ (p2 → p3)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134760840786455956982605364168 : ((((p1 ∨ False) → ((True → ((p2 → (False ∨ p4)) ∧ False)) ∧ (False → (p2 → (False ∧ ((p3 ∧ p4) ∧ p4)))))) → False) ∨ ((False → False) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300894283758990903659640017949 : (False ∨ (((((False ∧ ((p4 → ((True ∧ True) ∧ False)) ∨ p2)) ∧ p4) → False) ∧ p2) → ((True → (((False ∨ (p4 ∨ p4)) → p4) ∧ p4)) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177639647077102506454504511604 : ((((p1 ∧ ((False → ((p3 → (p2 → True)) ∨ p4)) → False)) ∧ p4) ∧ p3) ∨ (p4 → (False ∨ (False → (True ∧ (p4 ∧ (p2 ∧ (p2 ∧ p4)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56109797050859142881291677326 : ((((p5 → p4) ∧ (True ∨ p5)) ∨ ((False ∧ ((p5 ∨ (p3 ∨ ((p2 ∧ p4) ∧ (p3 ∨ p2)))) → (p3 ∧ ((p5 ∧ p2) ∨ p2)))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678494627651994319403785444295 : ((((((p3 ∨ True) → p5) ∧ ((True → (((True → ((p5 → p5) ∧ p4)) ∨ True) → False)) ∧ (p2 ∧ True))) ∨ ((True ∨ p5) ∨ (p4 ∧ p2))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118561495387158861025683669604 : ((p4 ∨ (((((False ∨ ((((False ∧ True) ∨ (p3 ∨ True)) ∨ True) ∧ ((False ∨ p3) ∨ (True → True)))) ∨ p3) ∨ p3) ∨ p5) ∧ True)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33999874538086658364959449157 : ((p5 ∨ (False ∨ (((True ∨ (p3 ∨ (False → (False → True)))) → (p2 ∧ p3)) ∨ ((((((p1 ∧ p1) → p1) ∧ p4) ∨ p2) ∨ p1) ∨ True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_58660948833484369880718775138 : (((p1 → p4) ∧ (((p4 → ((False ∨ (False ∨ p4)) ∨ p1)) ∨ (True ∧ p5)) → (p3 ∨ ((((p3 ∧ True) ∧ p5) ∧ (p3 ∨ p1)) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245819107413763516548746266126 : ((p3 ∧ p3) ∨ (p3 → (((((False → (p1 ∨ p3)) ∨ p4) ∧ (((p1 ∨ p5) ∨ p3) ∧ False)) ∧ (True ∧ True)) ∨ (False → ((p2 ∨ p2) ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797317048489451647255947249975 : (((p1 → ((((p2 → p5) → (((((p5 ∧ (False ∨ p2)) ∨ (p3 ∨ p5)) ∨ (True → False)) → p4) ∧ p5)) ∨ (p2 ∧ (p2 ∨ p1))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



