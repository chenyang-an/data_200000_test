variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87347537162553516459238253218 : ((((p1 → p4) ∧ ((True → p3) ∧ True)) ∧ (p1 ∧ (p5 → (((p3 → ((p4 → (p3 ∧ (p5 ∨ p4))) → (p3 ∧ True))) → p3) ∧ p4)))) → p4) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h10 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h11 := h4 h10
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262441701080050273648687081275 : (True ∧ ((p5 ∧ (p1 ∧ (((p4 ∨ p2) → (((p3 → (((False ∨ p4) ∨ (p2 → (p2 → True))) ∨ (p2 ∧ p1))) ∨ p2) ∨ p1)) ∧ False))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57250398599193163227769899679 : ((((p4 ∧ p5) → p1) ∨ ((p4 ∨ ((((True ∨ p2) → (p1 ∨ False)) ∧ (p5 ∧ p5)) ∨ (p2 ∧ (p1 ∧ p4)))) ∨ ((p2 ∧ p5) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142474454652328388101725686756 : ((p5 ∧ ((p1 ∧ ((p3 → p3) → False)) ∧ (((False ∨ (p1 ∧ False)) ∨ (p3 → p4)) ∧ ((p1 ∧ (True → False)) ∨ True)))) → (p4 ∧ (False ∧ p2))) := by
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
  let h8 := h5.left
  let h9 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h19 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h20 := h18 h19
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h22 : (p3 → p3) := by
        -- Implications on the right can always be decomposed.
        intro h23
        -- One of the premise coincides with the conclusion.
        exact h23
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h24 := h7 h22
      -- False on the left can always be used.
      apply False.elim h24
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h25 := h1.left
  let h26 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h27 := h26.left
  let h28 := h26.right
  -- Conjunctions on the left can always be decomposed.
  let h29 := h27.left
  let h30 := h27.right
  -- Conjunctions on the left can always be decomposed.
  let h31 := h28.left
  let h32 := h28.right
  -- Disjunctions on the left can always be decomposed.
  cases h31
  case inl h33 =>
    -- Disjunctions on the left can always be decomposed.
    cases h33
    case inl h34 =>
      -- False on the left can always be used.
      apply False.elim h34
    case inr h35 =>
      -- Conjunctions on the left can always be decomposed.
      let h36 := h35.left
      let h37 := h35.right
      -- False on the left can always be used.
      apply False.elim h37
  case inr h38 =>
    -- Disjunctions on the left can always be decomposed.
    cases h32
    case inl h39 =>
      -- Conjunctions on the left can always be decomposed.
      let h40 := h39.left
      let h41 := h39.right
      -- We want to use the implication h41 based on <expert-advice>. So we show its premise.
      have h42 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h41, we can now drive its conclusion.
      let h43 := h41 h42
      -- False on the left can always be used.
      apply False.elim h43
    case inr h44 =>
      -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
      have h45 : (p3 → p3) := by
        -- Implications on the right can always be decomposed.
        intro h46
        -- One of the premise coincides with the conclusion.
        exact h46
      -- We have shown the premise of h30, we can now drive its conclusion.
      let h47 := h30 h45
      -- False on the left can always be used.
      apply False.elim h47
  -- Conjunctions on the left can always be decomposed.
  let h48 := h1.left
  let h49 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h50 := h49.left
  let h51 := h49.right
  -- Conjunctions on the left can always be decomposed.
  let h52 := h50.left
  let h53 := h50.right
  -- Conjunctions on the left can always be decomposed.
  let h54 := h51.left
  let h55 := h51.right
  -- Disjunctions on the left can always be decomposed.
  cases h54
  case inl h56 =>
    -- Disjunctions on the left can always be decomposed.
    cases h56
    case inl h57 =>
      -- False on the left can always be used.
      apply False.elim h57
    case inr h58 =>
      -- Conjunctions on the left can always be decomposed.
      let h59 := h58.left
      let h60 := h58.right
      -- False on the left can always be used.
      apply False.elim h60
  case inr h61 =>
    -- Disjunctions on the left can always be decomposed.
    cases h55
    case inl h62 =>
      -- Conjunctions on the left can always be decomposed.
      let h63 := h62.left
      let h64 := h62.right
      -- We want to use the implication h64 based on <expert-advice>. So we show its premise.
      have h65 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h64, we can now drive its conclusion.
      let h66 := h64 h65
      -- False on the left can always be used.
      apply False.elim h66
    case inr h67 =>
      -- We want to use the implication h53 based on <expert-advice>. So we show its premise.
      have h68 : (p3 → p3) := by
        -- Implications on the right can always be decomposed.
        intro h69
        -- One of the premise coincides with the conclusion.
        exact h69
      -- We have shown the premise of h53, we can now drive its conclusion.
      let h70 := h53 h68
      -- False on the left can always be used.
      apply False.elim h70



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258646101648089138656602460880 : ((p5 ∨ p5) → ((p2 → ((((p4 ∧ p3) → (False ∧ (p1 ∧ True))) ∨ (((True ∧ p4) ∨ (((p1 → p4) ∨ p5) ∧ p4)) ∧ p4)) ∨ True)) ∨ p5)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264389964080565467825922236765 : (True ∧ (((True ∨ (p3 ∨ p2)) → p3) ∨ (((False ∨ (True → False)) ∨ (True ∧ ((p5 ∧ p5) ∨ False))) ∨ ((((p4 ∧ False) → p1) → p4) → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262119272923046904991391682000 : (True ∧ ((((True → (p3 ∨ (p2 → p1))) ∧ (((p4 ∧ (p5 ∧ False)) ∨ (True ∨ (((p2 ∧ (p5 ∨ p3)) → p4) ∨ p3))) → p5)) ∧ p5) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111446707473170194048531526704 : (((True → ((((p5 → p2) ∨ (p2 ∨ (p5 ∧ ((False → (p1 ∧ (True ∧ (False → True)))) ∧ p3)))) → (p4 ∨ p5)) ∨ False)) ∧ p3) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300379833539106240905981519611 : (False ∨ (((((p5 → p4) ∨ (p3 ∧ ((p4 → p3) ∨ (p5 → p1)))) ∧ (p3 → p3)) ∨ (p4 → ((p3 ∧ False) ∨ p2))) ∨ (p2 ∨ (False → p2)))) := by
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
theorem thm_5_vars_340963593881131886708727487160 : (p2 → (((p1 ∧ True) ∧ ((p4 ∨ (p4 ∧ p5)) ∨ ((p5 ∨ (p3 ∨ p5)) → ((p4 ∧ (p1 ∧ ((True ∧ (p4 → False)) → p3))) ∧ p3)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111589144144323757005639574291 : ((((p2 ∨ (p1 → ((((False ∧ (p1 → (p3 ∨ (p4 ∧ (True → p1))))) ∨ (True ∨ (False → p3))) ∧ p5) → p3))) ∧ p3) ∨ False) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185581477999238028465020645852 : ((p5 ∨ ((p3 ∨ ((p5 → (p2 → True)) → (p5 → p1))) ∨ p3)) ∨ ((False ∧ False) → ((((p1 → p2) ∧ p2) → (p2 ∨ (p3 ∧ p1))) ∨ False))) := by
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
theorem thm_5_vars_673232620864229627684381794385 : (((((False → ((p2 → (p2 ∧ True)) ∨ ((True ∧ p4) → False))) → ((((p3 ∨ (p5 ∨ p5)) → p2) → False) ∧ False)) → (False ∧ (p3 → p5))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → ((p2 → (p2 ∧ True)) ∨ ((True ∧ p4) → False))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (False → ((p2 → (p2 ∧ True)) ∨ ((True ∧ p4) → False))) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h7
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52600864801472056265049936716 : ((((p4 → ((False ∨ p5) ∧ (False → False))) ∨ (p4 ∨ (p3 ∧ (p2 ∨ p3)))) ∨ (p2 ∨ (((False ∨ p4) ∨ (p5 ∧ False)) ∨ (p1 → p1)))) ∨ p3) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249484845238255535418915925733 : ((p5 ∨ p1) ∨ ((True → (((True → True) ∨ p2) → ((p1 ∨ ((p5 → ((p5 → p2) → p2)) ∧ (p4 → True))) ∧ (p3 → p5)))) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40005235130335780662078305787 : (((p5 → ((p1 ∨ ((p4 ∨ p4) ∨ p3)) ∨ ((True ∧ (p1 ∨ (p1 ∨ ((p3 → p4) ∧ p5)))) ∧ (((p3 → p1) ∨ False) → p3)))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68083395063930547847140329693 : ((p2 → (p4 ∨ (((True → p2) ∧ (((True ∨ p5) → (p1 → (p2 ∨ True))) ∧ (True → (p1 ∨ (p1 ∨ p4))))) ∧ ((True ∨ p3) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136484639827079057295423328509 : ((((p5 ∨ p2) ∨ p3) ∧ (p5 ∧ ((p3 ∨ ((p3 ∧ ((p4 ∨ True) ∧ (((p3 → p1) ∨ p2) ∨ p1))) ∧ p1)) ∨ p1))) ∨ (p3 ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191208321136464505135628115679 : ((((p4 ∨ p1) → p2) → (((False → p5) → True) → p5)) ∨ (p2 ∨ (((p3 → (p1 ∨ (p2 → p2))) ∨ ((p5 ∧ (True ∨ p2)) ∧ p4)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337395000995578197745116058190 : (p1 → ((p4 ∨ (p4 ∨ (p2 ∧ ((p3 → ((((p1 ∧ (p5 → p4)) → p4) ∨ p2) ∧ False)) ∧ ((p4 ∧ p5) ∨ p5))))) ∨ ((p4 ∨ p3) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67441463287173436883717962660 : ((p1 → (((p2 ∧ ((p5 → (p1 → True)) → ((p5 → ((p1 → p2) ∨ p1)) ∨ p5))) ∧ ((p5 → True) → p4)) ∨ (p3 → (p1 ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698499984603516269783318707522 : (((((p5 ∧ ((p3 ∧ (p1 → True)) ∨ p2)) → (False ∨ (True → p1))) ∨ ((((p3 → (True → p1)) → ((True ∧ p5) → False)) ∧ p2) → p2)) ∨ p1) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116512996555001115242800976066 : (((p4 ∧ p4) ∧ ((True ∧ p1) ∨ ((False ∧ (((True ∨ ((p3 ∧ p1) → p4)) ∨ p4) ∨ p5)) ∧ (p1 → ((p4 ∨ p3) ∨ p1))))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229609839107091884550449361161 : ((p3 → (p5 ∧ True)) ∨ (((((p4 → ((p5 → (p3 → p1)) → p1)) ∨ False) ∧ (p1 ∧ True)) → (((False ∨ p5) ∨ p5) ∨ (p2 ∨ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48963118383229446905162967442 : (((((p3 ∨ (p4 → (((p2 ∨ (((p2 → True) → p2) ∨ p2)) ∨ ((p3 ∨ p4) ∧ p3)) → p3))) ∧ p1) ∨ False) ∨ ((p4 ∧ p1) → p1)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_148029579873250644762206818272 : (((((p1 → p4) ∨ p4) ∧ ((p1 ∨ p4) ∨ ((((False ∧ False) ∨ p2) ∧ True) ∨ (p3 ∧ p5)))) ∨ (p1 → p2)) ∨ (p1 → (p5 → (p5 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52781527897255949392708701248 : (((((True ∧ ((False ∨ (p4 ∨ p2)) ∨ True)) → (p4 ∨ p2)) ∨ (False ∧ False)) → (((p5 → p2) ∨ (True ∨ (p4 ∧ (p1 ∧ p3)))) ∧ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626889158169825812357024018440 : ((((p5 → (p4 ∧ ((True ∧ p1) ∨ (((p1 → p4) ∨ p1) ∨ ((p4 ∧ (((False → (p2 → (p4 ∧ p5))) → p5) ∧ p5)) → p1))))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249493981488806777924719950236 : ((p5 ∨ p1) ∨ ((p3 ∨ (False ∨ (p1 → ((p5 ∧ p4) → (p4 → ((p2 ∧ p4) ∨ p1)))))) → (((p4 → p4) ∧ (p4 ∨ (p3 ∨ p4))) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244397370858928219096170218460 : ((False ∧ p1) ∨ (((p3 ∨ ((p3 → p4) ∧ p4)) → p5) ∨ (((p3 ∨ True) → p4) ∨ ((p2 ∨ (p2 ∧ (p5 ∨ (p3 → p5)))) → (p5 → p2))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213117355687888976945631693502 : ((((p5 ∨ p2) ∧ p4) ∧ True) ∨ (p4 ∨ ((p2 → (((p3 → p3) ∧ False) ∧ ((False ∧ p2) ∧ True))) ∨ (((False → (p1 ∧ p2)) ∨ p5) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303712709687577230294191294294 : (p1 ∨ ((((((p3 ∨ p2) ∧ (((False ∧ p1) ∨ ((p3 ∨ (p4 ∧ p5)) ∧ p4)) ∨ ((p3 → p2) ∧ p1))) ∨ (p5 ∨ p1)) → p5) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_27965333931959754216259508254 : (((p2 → True) → (True ∧ (p5 → ((((p5 → p2) ∨ p3) → (p3 ∧ p1)) ∨ ((p5 ∧ False) ∨ (p4 ∨ (False → ((True ∧ p1) → False)))))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238257339899694148370355786989 : ((True ∨ p5) ∧ ((((True ∨ (True ∨ ((((p2 ∧ p1) → False) ∨ True) ∧ p5))) ∨ False) ∨ (p2 → p5)) → (p3 ∨ (((True → True) ∧ False) → p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h10
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- False on the left can always be used.
          apply False.elim h12
        case inr h13 =>
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
            -- Conjunctions on the left can always be decomposed.
            let h18 := h17.left
            let h19 := h17.right
            -- False on the left can always be used.
            apply False.elim h19
          case inr h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h21
            -- Conjunctions on the left can always be decomposed.
            let h22 := h21.left
            let h23 := h21.right
            -- False on the left can always be used.
            apply False.elim h23
    case inr h24 =>
      -- False on the left can always be used.
      apply False.elim h24
  case inr h25 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h26
    -- Conjunctions on the left can always be decomposed.
    let h27 := h26.left
    let h28 := h26.right
    -- False on the left can always be used.
    apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218013797248538397378573343777 : (((True ∨ p4) ∧ (p1 ∨ p4)) → (p4 → ((((p3 ∨ (p1 ∧ (p4 → (p2 → ((p4 ∨ (False ∧ p5)) ∧ p4))))) ∧ (p1 ∧ p5)) → False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
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
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233984297213319590620803216600 : ((p5 ∨ (p5 ∧ p5)) → (True ∧ ((False → (True → p3)) ∧ (True → (((True ∨ (True → (p4 → p1))) → p3) → (((False → p1) → p2) ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136813354683851414899639521413 : (((p5 → True) ∧ (((p3 ∨ (p1 → (True ∧ p4))) → (p1 ∨ (((p2 ∨ p4) → p2) → p1))) ∨ ((p3 ∨ p1) ∨ p1))) ∨ (p4 → (True → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134707491318152953004016828374 : ((((True ∨ (p1 → (p1 ∧ True))) → (((((False → True) → p4) ∨ (p4 ∧ p2)) → (False → (True ∨ p5))) ∧ False)) → p2) ∨ (p4 ∧ (p4 → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (p1 → (p1 ∧ True))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172312843535802507535489247030 : (((p4 ∧ (True → ((p5 ∧ (p3 ∨ p3)) → p5))) → (False ∧ (False → (p4 ∧ p1)))) ∨ (((((p1 ∧ p2) ∨ (p1 ∨ False)) → p3) → True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266207045531240396649481728497 : (True ∧ (p4 → (((True → p3) ∨ ((p2 ∧ p2) ∨ p5)) ∨ (((((True ∨ p1) → p5) → p1) → False) ∨ (p4 → (True ∧ ((p4 ∧ True) ∨ p1))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252318453046821326149311557837 : ((p4 → p5) ∨ (p4 → (p5 → (True → ((p3 ∧ (((p4 ∨ (p3 → p4)) ∧ p1) → (p4 → (p3 → False)))) ∨ (False ∨ ((False → p1) ∨ p4))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41873603055027686587055711195 : (((((p4 → p5) → p2) ∨ ((((True → (False → p4)) → p1) ∧ (p4 → ((p1 ∧ (p4 ∨ p1)) → ((True → p3) ∨ p2)))) → False)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59314817018108907784956501536 : (((p4 ∨ p1) ∨ (p4 ∧ ((True → (((p5 ∧ (False ∨ (((p5 → p5) ∨ (p4 ∨ p1)) → p4))) ∧ ((p2 ∨ True) ∨ p5)) ∧ p2)) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86631935052856253073715222562 : ((((p1 ∧ (p3 ∧ p3)) ∧ (p2 ∧ (False → p1))) ∧ ((False → p4) → ((((p2 ∧ True) → (p4 ∧ p5)) → p1) ∧ (True ∧ (p3 ∧ p5))))) → p5) := by
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
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h5.left
  let h11 := h5.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h12 : (False → p4) := by
    -- Implications on the right can always be decomposed.
    intro h13
    -- False on the left can always be used.
    apply False.elim h13
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h14 := h3 h12
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- One of the premise coincides with the conclusion.
  exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_398653161706868925271512355251 : ((((True → (((p5 ∧ True) → p4) ∧ ((((True ∨ ((True → ((True ∧ p2) ∨ (p2 ∧ False))) → p5)) → (p1 ∨ False)) ∧ p1) ∧ p1))) ∨ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336116700534125766005203019709 : (p1 → ((((p4 ∧ (True → (((p4 ∧ (p3 ∨ (True ∧ p3))) ∨ ((False ∨ p5) ∧ True)) ∨ (p3 → (False → p1))))) ∧ (p1 ∧ True)) ∨ p3) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343812736854899020947504369431 : (p2 → (p2 ∧ (((p4 ∨ (p2 ∨ p1)) ∧ ((p2 → p2) → ((p5 ∨ (((p1 ∧ (p2 → p1)) ∧ (False ∧ False)) ∨ p2)) ∨ p4))) ∨ (p5 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64868391271690212705503077738 : ((p2 ∨ ((p1 ∧ ((((p5 → (((p5 ∨ p2) → p4) ∨ (p2 → (True ∧ (p1 ∨ (p1 ∧ p4)))))) → p1) ∧ p2) ∨ p1)) ∨ (p5 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644171781076084019150546051639 : ((((True ∨ (True → (p5 → ((((p4 ∨ ((p2 ∨ (False ∨ ((True ∨ p5) ∧ p1))) ∨ p4)) ∨ p2) ∨ True) ∨ (p1 ∧ (False ∧ p1)))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678031036764350106005547442168 : (((((((p1 → True) ∧ ((p5 → p3) ∨ ((False ∧ False) ∨ (p4 ∨ p4)))) ∨ p5) ∨ ((p3 ∨ True) ∨ p3)) ∨ ((False → p1) ∧ (True ∨ p3))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254867197427723380575629362171 : ((p3 ∧ p5) → (p2 → (((p4 → p2) ∨ True) → (p2 → (((True → (p3 ∧ False)) → p4) ∧ ((p5 → (((False ∧ p1) ∨ True) ∨ p2)) → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h15 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h16 := h5 h15
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- False on the left can always be used.
    apply False.elim h17
  -- Implications on the right can always be decomposed.
  intro h18
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h1.left
    let h21 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h21
  case inr h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h1.left
    let h24 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123887431395159037909521770111 : (((p2 ∨ (((False ∨ (((p2 → p5) → (p4 → True)) ∧ p1)) ∨ False) → False)) → ((p4 ∧ (p2 → (p3 ∨ p5))) ∨ (True ∧ False))) → (p5 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84746339055632368898921180189 : (((((((p3 → True) ∧ p4) → p1) → p4) ∧ (((False ∧ False) → p4) → False)) ∧ (p5 → (((p3 ∧ p3) ∨ (False ∨ False)) → (p5 → p1)))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((False ∧ False) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h10 := h5 h6
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354774753347604253318735299819 : (p5 → (((((False ∨ p1) ∨ True) ∧ ((False ∨ (p1 ∧ p1)) ∨ False)) ∨ ((((p4 ∨ (p5 ∧ p4)) ∨ p5) ∧ (True ∨ (p3 ∨ p3))) ∨ True)) ∨ p4)) := by
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
theorem thm_5_vars_178277386958090418292320050634 : ((((p5 → p3) ∧ (False ∨ (((True ∧ p3) → p4) ∨ False))) ∧ (p5 ∨ p4)) ∨ (((p5 → p1) → p4) → ((p5 ∧ p2) ∨ (p3 ∨ (True ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135440965466395882196829390461 : ((((((((p1 → p3) ∨ True) ∧ p1) ∧ (True → ((p3 ∨ (p5 ∧ p1)) ∧ False))) ∧ p4) ∧ True) → (p4 → (False ∧ False))) ∨ ((p3 ∧ True) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h11 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h13 := h8 h12
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h17 := h8 h16
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- False on the left can always be used.
    apply False.elim h18
  -- Conjunctions on the left can always be decomposed.
  let h19 := h1.left
  let h20 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h21 := h19.left
  let h22 := h19.right
  -- Conjunctions on the left can always be decomposed.
  let h23 := h21.left
  let h24 := h21.right
  -- Conjunctions on the left can always be decomposed.
  let h25 := h23.left
  let h26 := h23.right
  -- Disjunctions on the left can always be decomposed.
  cases h25
  case inl h27 =>
    -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
    have h28 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h24, we can now drive its conclusion.
    let h29 := h24 h28
    -- We need to get the right conjuct of h29 based on <expert-advice>.
    let h30 := h29.right
    -- False on the left can always be used.
    apply False.elim h30
  case inr h31 =>
    -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
    have h32 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h24, we can now drive its conclusion.
    let h33 := h24 h32
    -- We need to get the right conjuct of h33 based on <expert-advice>.
    let h34 := h33.right
    -- False on the left can always be used.
    apply False.elim h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175109954496446258850570923289 : ((p4 ∧ (((p1 → ((p5 ∨ p1) → False)) ∨ (p4 ∨ p5)) → ((True ∧ False) ∧ p1))) → (((((p2 ∧ p1) ∨ p2) ∨ p3) ∨ (p5 ∨ p4)) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157035510973714209340677558129 : ((((p3 ∨ True) → (False ∨ (((False → ((((True ∧ p4) → p5) ∨ p2) ∧ p3)) → p4) ∧ p1))) ∨ p4) ∨ (True ∧ ((p4 ∨ True) ∨ (p5 → p2)))) := by
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
theorem thm_5_vars_207976042839727876136240539078 : ((((True → p4) ∧ p2) ∨ (p4 ∧ p2)) → ((p2 ∨ ((False → (True → p1)) → False)) → (p3 ∨ (((p2 → p1) ∧ p3) ∨ (p3 ∨ (p3 → True)))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168142543134699826265439986456 : (((p4 ∨ ((p2 ∧ p4) → p3)) → (True ∧ (p2 → (p2 → ((p1 ∧ (p5 ∧ p1)) ∨ p4))))) → (((p3 → False) ∨ True) ∨ ((p1 → p4) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671101738459159316902587736056 : ((((p1 ∨ (((((((p1 → p4) → p4) ∧ p5) ∧ (p5 ∧ p4)) ∧ p3) ∨ (((p4 ∧ p2) → p2) → p4)) → p2)) ∨ (True → (p2 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767122331844980355068036260748 : (((p4 ∧ (p4 → (((False → (p2 ∨ p5)) ∨ p2) → (p4 ∧ (((((p2 → (True → p3)) → (True ∧ p5)) ∨ True) ∨ (p5 ∧ p5)) → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310513838102504717416205627378 : (p2 ∨ ((p3 ∨ (p5 ∨ (p5 ∨ (p1 → False)))) ∨ (p3 → (((True → p5) ∧ ((p2 ∧ (False ∨ p2)) ∨ (False ∨ (p1 → p1)))) ∨ (False → p3))))) := by
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
theorem thm_5_vars_134157368814493891946770130905 : ((((((True ∧ p1) → (((p1 ∨ p4) ∧ ((True → p1) ∨ (p3 → p4))) ∨ p4)) → p4) → ((p5 ∨ p3) → p2)) ∨ p4) ∨ ((p4 ∧ False) → p2)) := by
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
theorem thm_5_vars_254746944930155864573693265850 : ((p3 ∧ p3) → (p4 → ((((False ∧ ((p1 → (((p3 → p2) ∧ p5) ∨ False)) ∧ p1)) ∧ (p1 ∨ p3)) ∨ ((p2 ∨ (False ∨ True)) ∨ p1)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740139403566830411527575318042 : ((((False ∨ p3) ∨ ((False ∨ False) ∨ ((False ∧ ((((p4 → p5) → (p2 ∨ (p4 → p1))) ∨ ((p2 ∧ p5) ∨ (p1 ∧ True))) → p3)) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41117828658551485839795613621 : ((((p3 ∨ (False ∧ (((p2 → ((p4 ∨ (p5 ∧ p3)) ∨ (p1 → p2))) → p4) ∨ (p3 → (p1 ∧ p1))))) ∧ (p1 → (p5 ∨ p3))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138441055613229173638027401263 : ((p5 → ((((p5 → p2) ∨ p2) ∨ p4) ∨ (((p4 → p1) ∨ p1) ∨ (((False ∨ (p4 → (p2 ∧ p1))) ∧ p2) → p4)))) ∨ (False → (False ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55219904764673725747030735247 : ((((p1 ∧ (p4 ∧ p5)) ∨ (p1 ∧ p2)) ∨ ((((True → (False ∨ ((p4 ∨ (p1 → (p1 ∧ p5))) → (False → p3)))) → p1) → p1) ∨ p2)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → (False ∨ ((p4 ∨ (p1 → (p1 ∧ p5))) → (False → p3)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138318036728021125772251228750 : ((p3 → ((True → False) → ((p1 → ((p3 ∨ p1) ∧ (False ∧ p4))) ∧ ((p5 ∧ ((p2 ∧ (True → p1)) ∨ p2)) ∨ p3)))) ∨ ((True ∨ p3) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134263430006071326417104342342 : (((((p3 ∨ p4) → p5) → ((False ∧ p5) ∧ (p1 → (p2 → (p3 → ((p3 ∧ (p5 → p4)) ∧ (p4 → p4))))))) ∨ p1) ∨ (p1 → (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309389976594238827277518948223 : (p2 ∨ ((p4 ∧ (p5 → (True → (p1 ∨ ((((p2 ∨ p1) ∧ ((p2 → True) ∧ (True → p3))) ∨ (p5 ∨ p1)) ∨ (False ∨ p1)))))) ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193023114051524740148992152729 : ((((p2 ∧ p2) ∨ (p5 ∨ (p5 → p5))) → (p4 ∧ True)) → (((p4 → (True → p3)) ∨ (True ∨ p5)) ∨ (p5 ∨ (True ∨ (p1 → (p1 → p3)))))) := by
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
theorem thm_5_vars_51195173936687211307972602070 : ((((p3 ∨ ((((True ∨ (True ∧ p2)) ∨ True) → (p4 → p3)) ∨ p3)) → (p2 ∧ (True ∨ True))) ∨ (p5 ∨ (False → (p2 ∧ (p4 → p3))))) ∨ p3) := by
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
theorem thm_5_vars_323252490228209853632713219061 : (p5 ∨ ((False ∧ (p4 ∧ ((True ∧ ((p2 ∨ ((True ∧ p5) ∧ (p1 → False))) → (p5 ∨ ((p4 ∧ False) ∧ True)))) ∨ (p2 ∨ True)))) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724417377850660203018014937546 : ((((True ∨ (p2 ∧ p3)) ∧ ((p1 ∨ ((((False → p2) ∧ ((p5 → (p2 ∧ p1)) ∨ p4)) ∧ (p3 ∧ (p5 ∧ p2))) → (p3 → p1))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199687090486713192139160393073 : ((((True → False) → ((p3 → p2) → p1)) → False) → (True ∧ (p3 ∨ ((p3 → ((p4 → (p4 → (p1 ∨ (p1 → p1)))) → (True → p1))) ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True → False) → ((p3 → p2) → p1)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177875311049360059568882439447 : (((((p5 ∧ ((p5 ∧ (p3 ∧ p4)) → (False → True))) ∨ True) → p2) ∨ p5) ∨ (True ∨ (p3 ∨ (p3 ∨ (False → (((False ∨ True) → p3) ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50213249141440432802424716848 : (((((((p1 ∧ (p3 ∧ (False ∧ p3))) ∧ p4) ∧ (p1 ∧ p1)) ∧ (p4 ∨ (False → (p4 ∨ p3)))) ∨ p5) ∨ (((True ∧ False) → True) ∨ p3)) ∨ p3) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619470326634277717843326084611 : (((((p3 ∨ (p3 ∨ True)) → (((True ∨ (((p4 → p2) → ((p3 ∧ p2) ∨ (p4 ∨ False))) → p4)) ∨ False) → ((True ∧ p4) → p5))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57862628830796100152244118772 : (((False ∨ (p2 ∨ p5)) → ((((((p2 → (p4 → p3)) ∨ p5) → p2) → (p1 ∨ (p4 ∨ ((p4 ∧ False) ∧ (p5 → p5))))) ∧ p2) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191459104958477084055361409821 : (((p4 → True) → (((p2 ∧ True) ∧ (p5 ∨ p5)) ∧ p4)) ∨ (p1 ∨ (((True ∨ True) ∨ ((p3 → p3) ∧ (p3 ∧ (p3 ∨ True)))) ∨ (p3 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314223724858669598210276046722 : (p3 ∨ (((((p2 ∨ p2) → ((p3 ∨ ((True ∧ False) ∨ p5)) ∨ False)) ∧ ((p4 → ((p5 ∨ p2) ∨ p2)) ∧ False)) ∧ p2) ∨ ((False ∨ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594705189350054246631354602625 : ((((((((p2 → p1) → p5) → (p4 → p4)) → ((p2 → (p2 ∧ p5)) → (p3 ∨ p3))) → ((True ∨ (p3 → (p4 ∧ p4))) → False)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137350869866661294623234987738 : ((p3 ∧ ((p4 ∨ (((p2 ∨ (p2 ∧ False)) → ((p5 ∧ True) ∨ ((((p3 → True) ∧ True) ∨ p2) ∧ False))) → p3)) ∧ False)) ∨ (False → (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49111142710247217088966270764 : ((((((((p4 ∧ p4) ∨ (True ∧ (False ∨ p3))) ∨ (p5 ∨ p1)) → True) ∧ p1) ∨ (((p5 ∨ p2) ∨ False) ∧ p4)) ∨ ((True → False) → p5)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200715597548505643104966246089 : ((p2 ∧ (False → (p3 ∧ (False ∧ (p3 ∧ p3))))) → ((p1 → p2) → (False ∨ ((p5 ∨ (p1 ∧ (True → (((p3 → p1) ∧ p1) ∧ p2)))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670148688980469257446191522008 : (((((((True ∧ p5) ∧ (p5 ∨ p4)) ∨ True) → ((((p4 → p2) ∨ True) ∧ (p5 ∨ ((p4 ∧ p1) ∨ False))) ∧ False)) ∨ (p3 ∨ (True ∨ p2))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675494874443073363602810456675 : (((((p1 → (((((p4 → (p3 ∨ p1)) → p3) → (((p3 ∨ p2) → p4) ∨ True)) → p1) → p4)) → p3) ∧ (p4 ∧ (False ∧ (p2 → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173125789048597199581865937009 : ((p2 ∨ (True ∧ ((False ∧ p4) ∨ (((p4 ∨ (p4 ∨ False)) → False) ∧ (p5 → p2))))) ∨ (((True ∧ p4) → p5) → ((p5 → (True → True)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309012812822373955894150472694 : (p2 ∨ (((True → (p3 ∧ p5)) ∧ (((p4 ∨ p5) → p5) ∧ ((((p5 ∧ ((p1 ∧ p2) ∨ p2)) ∧ p3) ∨ (False → p2)) → (p2 ∨ p2)))) → p3)) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808924997088133907959206596185 : (((p5 → (((((((((p1 → p3) ∨ p4) ∨ p3) → (p2 ∧ False)) ∨ (True ∧ (True ∧ p5))) ∧ p2) ∧ (p3 → True)) ∨ (False ∨ p4)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64044609976782471532377029027 : ((False ∨ (((((False ∨ p3) ∧ (True ∨ ((((p1 → ((p5 ∧ p2) ∧ p4)) → True) ∧ True) → p3))) → True) ∧ p5) → (p2 ∨ (p5 ∨ False)))) ∨ p4) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307635849217278651152503709454 : (p1 ∨ (p1 → (((p4 ∧ p3) ∧ True) ∨ (p2 ∨ ((p4 → ((True → ((p5 ∧ p2) ∨ p4)) ∧ (False → ((p2 → False) → p3)))) ∧ (True ∨ p3)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173300647420206397765531232987 : ((p1 → (((p3 → (p2 → False)) ∨ p1) → (((p4 ∨ p4) ∧ (p1 → p2)) ∧ False))) ∨ (False ∨ ((True ∨ p2) ∨ (p5 ∨ ((p3 ∨ p4) ∨ p2))))) := by
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
theorem thm_5_vars_197287563069652949610140816165 : (((((p2 ∨ False) ∧ p1) → (p3 ∨ p2)) → p3) ∨ (((False → p3) ∨ (p1 ∧ False)) ∨ (p1 → ((p3 → p3) → (p1 ∧ ((p5 ∧ p2) → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243904575026464039028878135567 : ((True ∧ False) ∨ ((((False ∧ (((False ∨ (False ∨ (p4 ∨ p3))) → p3) → (True ∧ p4))) ∨ True) ∨ p5) ∨ ((((True ∨ p1) → False) → p1) → p2))) := by
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
theorem thm_5_vars_308668843669644094083167999593 : (p2 ∨ ((p5 ∧ (((False ∧ True) ∨ ((((((((p1 → p4) ∧ p4) ∧ p4) ∨ (p3 ∨ p2)) ∧ False) → p3) ∧ (False → True)) → p2)) ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147708802316255851291542358746 : (((((p5 → True) ∧ (p5 ∧ ((True ∧ p4) → (p4 ∨ p5)))) ∨ (((p5 ∨ True) → (p3 ∧ False)) → p4)) → p4) ∨ (p5 ∨ (True ∨ (False ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52418841977509746617748888256 : ((((p5 ∧ True) ∧ ((p2 ∧ (False ∧ (False ∨ p2))) ∨ ((p1 ∧ True) ∨ p1))) ∧ (((((p3 ∨ False) ∧ True) ∧ p4) → p3) ∧ (True ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



