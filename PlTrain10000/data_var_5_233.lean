variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353414801830262353622685835059 : (p4 → (p1 ∨ ((p2 → (((((p3 ∧ (p3 ∧ p2)) ∨ p5) ∧ p1) ∨ True) ∨ (p5 ∧ (((p5 ∧ True) → p2) → ((p1 → p5) → p3))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134085977873437700558193837965 : (((((True ∨ (p3 → p4)) ∧ ((p3 ∨ True) ∨ (p2 → ((p5 → (((p1 ∨ True) ∧ p4) ∨ p5)) ∧ p1)))) → False) ∨ True) ∨ (False → (p5 ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248765808821989058784960368937 : ((p3 ∨ p3) ∨ (((((True ∧ True) ∨ (p1 → (p3 ∧ (p2 ∨ p4)))) ∨ p4) → False) ∨ (True ∧ (p2 → (False → ((p3 ∨ True) → (False ∧ False))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340753900010363810792407085359 : (p2 → ((((False → p3) ∧ (((True ∨ ((p3 → True) ∧ ((p3 ∧ (p2 → p4)) ∧ p2))) → True) ∧ ((p3 ∧ (p5 → p2)) → False))) ∨ True) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659065961372129635828345088569 : ((((p2 → ((((((p3 → ((((p3 ∧ (p2 → p2)) → p2) → p5) ∧ False)) → True) ∨ False) → False) → True) → (p2 → p3))) ∨ (True ∨ p4)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_346773404168315458542164178047 : (p3 → (((p1 ∧ (p1 → ((p1 ∨ (((True ∨ p4) ∨ True) → False)) ∨ ((False ∨ p5) → (p5 → True))))) → False) ∨ (False → (True → (True ∨ True))))) := by
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
theorem thm_5_vars_181609915758289239695363620159 : ((p2 → ((((True ∧ p5) ∨ ((p4 → p5) ∨ (p5 ∧ p5))) → p2) → p3)) → (((p3 → False) → (p5 ∧ p1)) ∨ ((True ∨ (p1 → p5)) ∨ p1))) := by
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
theorem thm_5_vars_307138671023958092741828124206 : (p1 ∨ (False ∨ ((False ∨ ((((p1 ∨ p1) ∨ (p3 ∨ (p1 ∨ (p1 ∧ ((p4 → p2) ∧ p4))))) → p4) ∧ p3)) → ((p2 ∨ p3) ∨ (True → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178470346057495859470267788089 : (((((False ∨ False) ∧ ((False → p3) → p1)) ∧ False) ∨ (p3 ∨ (p1 → p2))) ∨ (True ∧ (False → ((p3 ∨ ((p2 → p3) → p1)) ∧ (p4 ∨ p3))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209135162092554588093453987903 : ((p3 ∨ (((p3 ∧ p1) ∧ p3) ∨ p1)) → ((True → (False ∧ (p2 ∨ False))) → ((p4 ∨ (p1 → (p2 ∨ (False → ((p3 ∧ True) ∨ p1))))) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h14 := h2 h13
      -- We need to get the left conjuct of h14 based on <expert-advice>.
      let h15 := h14.left
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h18 := h2 h17
      -- We need to get the left conjuct of h18 based on <expert-advice>.
      let h19 := h18.left
      -- False on the left can always be used.
      apply False.elim h19
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h20 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h21 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h22 := h2 h21
    -- We need to get the left conjuct of h22 based on <expert-advice>.
    let h23 := h22.left
    -- False on the left can always be used.
    apply False.elim h23
  case inr h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- Conjunctions on the left can always be decomposed.
      let h28 := h26.left
      let h29 := h26.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h30 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h31 := h2 h30
      -- We need to get the left conjuct of h31 based on <expert-advice>.
      let h32 := h31.left
      -- False on the left can always be used.
      apply False.elim h32
    case inr h33 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h34 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h35 := h2 h34
      -- We need to get the left conjuct of h35 based on <expert-advice>.
      let h36 := h35.left
      -- False on the left can always be used.
      apply False.elim h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135974226192141299762477852308 : ((((p2 → (((p1 ∧ (p1 → False)) ∨ False) ∧ p1)) ∧ False) ∨ ((p1 → True) ∨ (False ∨ ((p1 ∧ False) ∧ (p1 ∨ p4))))) ∨ ((p3 → p4) ∧ False)) := by
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
theorem thm_5_vars_714519272610516400162230562565 : (((((True → False) ∧ ((p2 → p3) ∨ p5)) → ((False ∧ (p2 ∧ p3)) ∨ ((False → p2) ∧ (p3 → (p3 ∨ ((True ∨ (p1 → True)) → True)))))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48713611986182814357986555151 : ((((p1 ∧ (p4 → (p3 ∧ p4))) ∧ ((p1 ∧ ((False ∨ p4) → True)) ∨ ((p4 → (p4 ∨ p3)) ∧ (False ∧ p4)))) ∧ ((p5 ∨ False) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56078369813264492411834946564 : ((((p3 ∨ (p2 ∨ p2)) → False) ∨ ((p3 ∨ (p2 ∧ ((True ∧ p1) ∨ (p4 ∧ p2)))) → (p2 ∨ (((False ∧ p2) ∧ (True ∨ p2)) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608696942743318200445021609716 : ((((((((True ∨ ((p2 → (p2 ∧ p1)) → ((True ∧ p1) → (p4 ∨ (False ∧ p2))))) ∧ (p3 → p3)) → True) → (p3 → False)) ∨ p4) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_114842040361168953005011630574 : ((((p5 ∧ (((p5 → (p5 → (p3 ∨ False))) ∨ (p3 → p5)) → False)) ∧ False) ∨ (True ∨ ((((p5 → True) ∨ False) → p4) → p5))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61423755631669981347084798014 : ((p1 ∧ ((((True ∧ (p5 ∧ ((True → ((((p4 ∧ False) ∨ p4) ∧ False) → p1)) ∨ (p3 ∧ p3)))) ∨ p2) ∨ (p2 ∨ (p1 → p4))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51500120074787482434148607186 : ((((True → (True → p2)) ∧ ((True ∧ (p1 ∨ p4)) ∨ ((p3 ∧ p3) ∧ (p2 ∧ (p2 ∨ True))))) → (p5 ∧ ((p1 ∨ p1) → (p3 ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113686199537603551913411391615 : (((((p2 → ((True ∧ p1) ∧ (((p5 ∧ p1) ∧ ((((p4 ∧ p1) → p1) ∧ p3) ∨ p1)) → False))) ∨ p1) → p1) → (p4 → p2)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261289615883706184350458656500 : ((p5 → True) → ((p2 ∨ p4) → (((p1 → p5) ∧ (False → (False ∧ p3))) ∨ ((False → False) → (True → ((p4 ∨ ((False ∨ True) → p2)) ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47027804451737642706005717560 : ((((p2 → ((p1 ∨ p2) → (p1 ∧ ((p1 → ((((True → p2) ∧ True) → (False → True)) ∨ (p1 ∧ True))) ∧ True)))) → p1) ∨ (True ∨ False)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962882693985771505228010597771 : ((((False → p5) ∧ (((p4 ∨ (p5 → p5)) ∧ ((False ∧ (p4 ∧ False)) ∨ True)) ∧ ((p2 → (((p1 ∨ p2) ∧ p5) ∨ p2)) → (False ∧ True)))) → p2) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h12 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h13 : (p2 → (((p1 ∨ p2) ∧ p5) ∨ p2)) := by
        -- Implications on the right can always be decomposed.
        intro h14
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h15 := h5 h13
      -- We need to get the left conjuct of h15 based on <expert-advice>.
      let h16 := h15.left
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- False on the left can always be used.
      apply False.elim h19
    case inr h21 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h22 : (p2 → (((p1 ∨ p2) ∧ p5) ∨ p2)) := by
        -- Implications on the right can always be decomposed.
        intro h23
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h23
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h24 := h5 h22
      -- We need to get the left conjuct of h24 based on <expert-advice>.
      let h25 := h24.left
      -- False on the left can always be used.
      apply False.elim h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200441184471486814768149846881 : (((p5 ∨ False) ∨ (((False ∨ True) → p1) ∨ p1)) → (p3 ∨ (p3 → (p5 ∨ (True → ((((p5 ∧ (p5 → (p3 ∨ p4))) ∧ True) ∧ p5) → p5)))))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- Implications on the right can always be decomposed.
      intro h20
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h21.left
      let h24 := h21.right
      -- Conjunctions on the left can always be decomposed.
      let h25 := h23.left
      let h26 := h23.right
      -- One of the premise coincides with the conclusion.
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55533615220864581342370608717 : ((((False → p1) → (p1 → (p1 ∨ False))) → ((p5 → ((p3 → False) → (((p3 ∨ False) ∧ (((p2 → False) → p4) ∧ p3)) ∧ p3))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49064155745082801879686676728 : (((((((True ∨ True) → p4) → (False ∨ ((p4 ∧ (p1 → p3)) ∧ p5))) ∨ (p4 ∧ (p5 ∨ p3))) ∨ (False → True)) ∨ ((p4 ∧ True) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353972894075827210489080101485 : (p4 → (p3 → (((((((p5 ∧ p1) → (((True ∨ (p3 ∧ p5)) → p3) ∧ True)) ∧ False) ∧ p3) ∨ (p5 ∨ p1)) ∧ p1) ∨ (p5 ∨ (p1 → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258494539919969119505665456607 : ((p5 ∨ p2) → ((p3 ∨ p3) ∨ ((p5 ∨ (p2 → ((p2 → p5) ∧ (p1 ∨ p2)))) ∨ ((p1 → (True → ((p2 ∧ p4) ∧ (p1 → p5)))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166431026269362884935934588024 : ((p1 ∨ (p4 ∧ ((((False ∨ (((p1 → p3) ∧ p5) ∧ (False ∨ p1))) → p3) → p5) ∨ True))) ∨ (((True ∨ (p5 → (p2 → p4))) ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60064549565401387886179188985 : (((p2 ∨ p2) → (((p3 → ((True ∧ p5) → (((p2 ∧ p5) ∧ ((p3 ∨ False) ∨ (p2 ∨ (True ∧ (p5 ∧ p2))))) ∨ p3))) → p5) ∨ True)) ∨ p4) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670383232549215861404079275869 : (((((p2 → (p2 → p4)) ∨ (((p4 ∧ ((p1 ∨ p4) ∨ (p1 ∧ ((p3 ∨ True) ∨ False)))) ∧ (p1 ∨ p4)) ∨ False)) ∨ (p5 → (p5 ∨ p4))) ∨ p5) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125533478988676114027597396099 : (((True → False) ∧ (p3 ∨ ((True → (((False ∧ True) ∨ (p5 → (((p4 ∨ p3) → (True ∨ p2)) → True))) ∨ p4)) → (p5 → p1)))) → (p3 → p5)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h9
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204688450824098660222543744603 : (((p2 ∨ ((p4 ∧ p4) ∨ p1)) ∨ p5) ∨ (((p4 ∧ (((p3 ∨ (((p2 ∧ (p3 → p5)) → (p3 ∧ True)) ∨ p2)) → p3) ∨ p3)) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713067592135373626019306232214 : ((((p4 ∧ (p3 ∧ ((p4 ∨ p3) → p4))) ∨ (((((True ∧ (p4 ∨ (p2 ∨ p3))) → p2) ∧ ((p1 → (p1 → True)) ∧ False)) ∨ p2) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201169990579329453189497980382 : ((p1 → (((False ∨ p3) → (p1 → p3)) ∧ p2)) → (((((p5 ∧ p4) → p4) → p4) ∧ ((True → p5) ∨ (((p4 → p3) ∧ p1) ∨ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117342200645511938576081178066 : ((False ∧ ((p5 ∨ p2) ∨ (p3 ∧ ((True ∨ ((p2 ∨ ((p1 ∨ True) → (False ∧ p5))) ∧ False)) ∧ ((p5 → (p3 → p4)) → p2))))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49218325585938027106177731375 : ((((p5 ∨ True) ∧ ((((p2 ∧ p4) ∧ p4) ∧ (((p3 → p4) ∧ False) ∧ True)) ∧ (p5 ∨ ((True → False) ∨ p3)))) ∨ ((p2 → p5) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46381742073732399610107804308 : ((((p4 ∧ ((False ∨ p5) ∧ ((p1 → (False ∧ False)) ∧ p4))) ∧ ((((((False → p1) ∧ p1) ∧ p5) ∧ p5) ∨ p1) ∧ False)) ∧ (p2 ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704026650785459146231448553485 : ((((((True → (p2 ∧ True)) ∧ (p2 ∨ (p1 → p5))) → p5) → (((p4 ∨ p3) ∨ False) → ((False → p2) → ((p3 → (p1 ∨ False)) ∨ True)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- False on the left can always be used.
    apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164760480088000313403831448549 : (((((p3 ∨ ((p3 ∧ p3) ∨ (True → p4))) → (p1 ∧ False)) ∨ (p3 ∨ (p2 → True))) ∨ p3) ∨ (((False ∧ p4) → (p5 → p3)) → (True ∧ p2))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615110941016183624983389542263 : ((((((((p3 → (((True ∨ ((p1 ∨ p3) ∧ p3)) → p5) ∧ p1)) → False) ∨ p4) ∨ p2) ∧ (((p1 ∧ (p3 → False)) ∧ p1) ∨ True)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_186204730607885715414012481143 : (((p3 ∨ (((True ∧ (p5 → False)) → (p2 → p5)) → p2)) ∨ p3) → ((p3 ∧ ((((p3 ∨ p3) → p4) ∧ p5) ∧ (p1 ∧ (p5 ∨ False)))) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52619935155523803686461461626 : (((((True → p2) ∨ p2) ∨ ((((p5 ∨ (p3 ∧ p5)) → False) ∧ p3) ∧ p3)) ∨ ((False ∧ (p2 ∧ p3)) ∧ ((p1 → (p1 ∧ True)) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338386252250921908719501211876 : (p1 → ((p3 → ((p2 ∧ p3) ∨ p5)) ∨ (p3 ∨ (p5 → (False ∨ ((p4 ∧ p2) ∨ ((p1 → (p2 ∨ p1)) ∨ (p1 ∧ (p3 → (p2 → p3)))))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198635911329736463058572846897 : ((p3 ∨ (((p1 → (p2 → p5)) ∨ p2) → p3)) ∨ ((p1 ∨ p5) ∨ ((((((p1 ∧ p5) ∨ p3) → p2) ∨ (p5 ∧ (p5 ∨ p3))) ∨ p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49802202073080283719764641280 : (((True → ((p3 ∧ p1) ∨ (((p2 → p1) ∧ False) ∨ ((((p3 ∨ False) ∨ (p4 → (False → False))) → p2) → False)))) → (p2 ∨ (p3 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215144808709405850725447364402 : (((p5 → p2) → (p4 ∧ p5)) ∨ ((((((False ∧ False) ∨ True) ∨ p3) → (True ∧ (p5 ∨ (p5 ∨ p1)))) ∨ ((p3 ∨ p1) ∨ (p3 ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_34208531251622065525876312043 : ((True → ((p1 ∨ ((((((False ∧ (p1 ∨ p2)) ∨ ((((False → p5) → True) ∨ p5) ∨ p1)) ∧ p1) → False) ∨ p2) ∨ p4)) ∨ (True ∨ p5))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314638382214069816594266763676 : (p3 ∨ (((((p2 ∧ p2) ∨ ((p1 → (False ∨ True)) ∧ ((p5 ∧ False) → p2))) ∨ p3) ∧ p3) ∨ ((True ∨ p5) ∧ ((p3 ∧ p4) → (p5 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198207273068974708960221668526 : (((p4 → p1) → ((p1 → (p2 ∧ True)) ∨ False)) ∨ (p2 ∨ ((False → (p5 ∨ (p3 → ((p5 ∧ p1) → p2)))) ∨ (p5 ∧ (p3 ∨ (False ∧ False)))))) := by
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
theorem thm_5_vars_53860341954914660405667103145 : (((((False ∧ p1) ∨ p5) → (p2 ∧ ((False ∨ p1) → p5))) ∨ (p3 → (((p1 → (p4 ∧ ((p3 → p5) ∧ p5))) → p4) → (p2 ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50274155347811419352988804629 : (((((((p5 → (p1 → True)) ∧ (((False → p1) → True) ∨ p5)) → p1) ∨ (p1 ∧ True)) ∨ (p1 → True)) ∨ ((p1 → p5) → (p1 ∨ p4))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737960296273981468275067666592 : ((((True ∧ p4) ∨ ((((((p5 ∧ p1) ∧ (False ∧ (p3 ∧ True))) ∧ ((p1 → p4) → p2)) ∨ True) ∨ (p4 → (False ∨ True))) ∨ (p3 ∨ p4))) ∨ p2) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178352529080158058368948425046 : (((False ∨ (((p1 ∧ ((p2 ∧ p5) ∨ p2)) ∧ p4) ∧ p4)) ∨ (p1 ∧ p5)) ∨ ((p4 → p4) ∨ (((False ∨ (True ∧ p3)) ∨ p3) → (False ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179368155993976042665066755697 : ((p2 ∨ ((p3 ∧ p3) ∧ ((p4 → (p5 → p3)) ∨ ((p2 → p1) ∧ p3)))) ∨ (p1 → (p1 ∨ (p1 ∧ (((True ∨ (p1 ∧ True)) ∨ True) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46014531944107978834211387612 : (((((p3 → (True → (p3 ∨ (p2 ∨ p2)))) ∧ (((p5 ∨ p1) ∨ p3) ∧ ((((p4 → p3) ∨ p2) ∧ False) ∨ p5))) ∧ p5) ∧ (p2 → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600239247885156848706308191152 : (((((p2 → p2) → (((True ∨ p4) → (p3 → p3)) ∧ ((((p2 ∨ p1) ∧ (((p4 → p5) ∨ p4) ∨ (p2 ∧ False))) → p2) → False))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609929286149425623955460548697 : (((((p4 → ((((((((True → p1) ∨ p1) → (p3 ∧ p2)) → (False ∧ p4)) → (True ∧ p3)) → p3) ∨ p2) ∨ (p3 ∨ p4))) ∨ p2) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_323945260379700387257054064844 : (p5 ∨ ((p5 ∨ ((((True ∧ p4) ∨ (p2 ∨ p3)) ∨ (((True ∨ p2) ∧ p5) ∨ p1)) ∧ p1)) → ((True ∧ ((p5 → False) ∨ (False → p4))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
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
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- False on the left can always be used.
          apply False.elim h14
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h20 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h21
          -- False on the left can always be used.
          apply False.elim h21
        case inr h22 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h23
          -- False on the left can always be used.
          apply False.elim h23
      case inr h24 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h25
        -- False on the left can always be used.
        apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39872077592702294122134082383 : (((p2 → ((((((p3 ∨ p2) ∨ False) ∧ (p3 ∨ (p1 ∨ (p4 ∨ (p3 ∨ False))))) → ((p2 ∧ p4) ∧ (p2 ∨ p4))) ∨ p3) → p4)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234030876778712103594923027332 : ((p5 ∨ (False → False)) → ((False → p2) → ((False → p2) ∧ ((True → ((p5 ∨ p4) ∨ p5)) ∨ ((False ∨ True) ∧ (((True ∨ False) ∨ p3) ∨ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336350780914351912851014817688 : (p1 → (((True ∧ p3) ∨ (((False → (((((p4 ∨ (p3 → p3)) ∧ True) ∧ (p4 → True)) ∨ p3) ∨ ((False ∨ p3) ∧ p1))) → p2) ∨ p1)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346591592339685390798001673788 : (p3 → ((((((True ∨ False) ∧ p1) ∨ (p4 ∨ (p3 → p1))) → ((((True ∨ True) → p2) ∧ False) ∨ (p5 ∨ p4))) ∨ p1) ∨ ((p2 ∧ False) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686055429507429870738571712844 : ((((((p5 ∧ p5) → ((p3 ∧ ((False ∨ p2) → (p4 → (p2 ∧ p1)))) ∧ p5)) → (True → False)) → (p5 → (p1 → ((p1 → p4) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309680407458610858676153733558 : (p2 ∨ ((((p1 ∨ p2) ∧ ((p1 ∧ ((True → True) ∨ ((p3 ∧ (p1 → (p5 ∨ True))) ∧ p1))) ∧ (True → True))) → p3) → ((p5 → p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653550606103451369216770161169 : ((((p5 → (p2 ∨ (((p3 ∨ ((p4 → True) → p1)) → (False ∧ (p3 → ((p4 ∧ False) → ((p4 ∧ p2) → p3))))) ∧ p4))) ∧ (p3 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60789236404081734775409438222 : ((True ∧ (True ∧ (((((p5 ∨ False) ∨ (p3 → ((False ∨ True) ∨ p4))) → p5) ∧ ((True ∧ p1) ∧ (p3 ∨ p2))) → (True → (True → p5))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h10 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h11 : ((p5 ∨ False) ∨ (p3 → ((False ∨ True) ∨ p4))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h13 := h4 h11
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h15 : ((p5 ∨ False) ∨ (p3 → ((False ∨ True) ∨ p4))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h17 := h4 h15
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148043745656555489073565369806 : (((False ∧ (((p5 ∨ (False ∨ p5)) → (False → p5)) ∧ (p5 ∨ ((p2 ∧ p5) ∨ (p5 ∨ p2))))) ∨ (p4 → True)) ∨ (p3 ∨ ((p1 ∧ p4) ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657953085623182244778219704241 : ((((p1 ∧ (True → (p1 ∨ (p1 ∧ (((((True ∨ ((p4 ∨ ((p2 ∧ p2) ∨ True)) → True)) ∧ p5) ∧ p5) ∧ False) ∨ p5))))) ∨ (True → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57445621178040397017876897436 : (((p4 ∨ (True → p1)) ∨ (((p4 → (p1 → (p2 → ((False ∧ (p3 → p1)) ∨ (p1 → p3))))) → ((True → p4) ∨ (True ∨ False))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748711739106895196377340587061 : ((((p3 → p4) → (((False ∨ (p1 ∧ p4)) → ((p2 → (p2 ∨ True)) ∧ ((p1 ∧ p3) → p2))) → (((p5 → (p1 ∧ True)) → True) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43076358850206217086254017503 : (((((((p2 ∧ (p2 ∧ (p2 → p4))) → (((p5 ∨ p1) ∧ (False ∨ p4)) ∨ ((p5 ∧ p3) ∧ p5))) → p5) ∧ (False ∨ p3)) ∧ p2) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230469648881103093290651133538 : (((p5 ∨ p3) ∧ p5) → (((((p2 → p3) ∧ (((True ∨ p4) ∧ p3) ∧ p1)) ∨ True) ∧ p2) → (False ∨ (p3 → (((p5 ∨ p5) ∧ p4) ∨ p2))))) := by
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
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h1.left
      let h14 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h1.left
      let h21 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h23
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h25
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
  case inr h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h1.left
    let h28 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h29 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h30
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h31 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h32
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308444135257623629007521630307 : (p2 ∨ (((p3 → (p4 ∧ ((((p1 → p2) → (True ∧ p2)) ∨ (p3 ∧ False)) ∨ (p1 → (((p5 ∨ p5) → (p3 ∧ True)) ∧ p5))))) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44097932706679320571980363388 : ((((p4 → (((p3 ∨ p4) ∧ (p3 ∧ (((p1 → (p5 → p5)) ∨ p5) ∧ ((p4 → True) ∨ False)))) ∧ False)) ∧ ((p4 ∨ p2) ∧ p3)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301277144435205095412731736868 : (False ∨ (((p2 ∨ (p1 → (p3 ∨ p1))) ∧ p3) → ((((p3 ∧ (p3 → (p5 ∧ True))) → (p1 ∨ p5)) → (p4 ∧ True)) ∨ (p5 → (p5 ∧ p5))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192935472706234836941769866796 : ((((False → (p1 ∨ p3)) ∧ (True → False)) ∨ (p4 ∧ False)) → ((True ∧ ((p1 ∧ ((False ∨ p1) → (True → p4))) ∨ p5)) ∨ ((p2 ∧ p4) ∨ True))) := by
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
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340804702777970316725399880362 : (p2 → (((p2 → ((((((((p3 → p5) ∨ False) ∨ (p5 → True)) → (False ∨ p2)) → p3) ∨ (True ∧ p1)) ∧ False) → (p2 ∨ False))) → p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167143267389517083210092346763 : ((((p1 ∨ (p4 → (False ∧ True))) ∧ (p4 ∧ ((p2 ∧ p5) → (p1 ∨ (p1 → False))))) ∨ False) → ((True → (p1 ∨ ((p2 ∨ p1) ∧ p3))) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h5.left
      let h11 := h5.right
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h12 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h13 := h9 h12
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h18.left
      let h21 := h18.right
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h18.left
      let h24 := h18.right
      -- One of the premise coincides with the conclusion.
      exact h23
  case inr h25 =>
    -- False on the left can always be used.
    apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137116059801911225828849672663 : ((True ∧ (((p2 ∨ True) ∨ (False ∧ (True ∧ False))) ∧ (p5 ∧ (p1 ∨ (p3 ∨ ((p5 ∨ p4) ∨ (True ∧ (p1 ∧ p5)))))))) ∨ ((p2 → True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769979002325099723966624512775 : (((p5 ∧ (p1 → ((False → ((False ∧ p1) → (p3 ∧ p3))) → (p5 ∧ (p4 → (p3 ∧ ((p2 → ((p5 ∨ (p4 ∨ False)) ∨ False)) ∧ p1))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190392568627879554133825979721 : (((p1 ∧ (((p3 ∨ (True → p1)) → p2) → p3)) ∨ True) ∨ (((p5 ∧ ((p3 ∨ (False → p5)) ∧ p2)) ∧ p4) ∨ (p4 → (p5 ∧ (False ∨ p5))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303891377759897019450439264171 : (p1 ∨ (((((p3 → ((p4 ∧ False) ∧ (p4 ∨ (p5 → (p1 ∧ (False ∨ p2)))))) ∨ True) ∨ True) ∨ ((False ∨ ((p5 ∧ p2) ∨ p4)) ∨ p4)) ∨ p1)) := by
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
theorem thm_5_vars_260052918334292796895847448231 : ((p2 → False) → (((p4 ∨ (True ∨ p1)) ∨ (((True → p1) ∧ (p1 ∧ (p2 ∨ (p2 ∨ p5)))) ∨ (((p3 ∧ p5) → True) ∨ p2))) → (False ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
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
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h15 =>
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
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190729175598986751350699002609 : ((((p1 ∧ p1) ∨ (p3 → (p1 ∧ p3))) ∧ (True ∧ p2)) ∨ (False ∨ ((((p1 → True) ∨ ((((False ∧ p4) → p5) ∨ True) → p2)) → True) ∨ p2))) := by
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
theorem thm_5_vars_177868362101139026156504663163 : ((((p3 ∨ ((False ∧ p1) ∧ (p4 ∧ ((p4 ∧ p2) → p3)))) ∨ p1) ∨ True) ∨ ((p3 ∨ (True ∧ (p1 → (((True ∨ False) → False) → False)))) ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611052423619146149041320696791 : ((((((True ∧ (p2 ∧ (True ∧ (False ∧ True)))) → ((p3 ∧ p5) ∧ (True → (True → (False → ((p3 ∧ (p4 → True)) ∨ p1)))))) → False) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135168779141465139618766186426 : (((((p5 → p3) ∨ ((True ∨ ((((p2 ∧ p2) → p5) ∨ p1) ∨ (p2 ∨ p2))) ∨ (p1 ∨ p5))) ∧ p3) → (p4 → p1)) ∨ ((True ∨ p4) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330591798864913524452759164675 : (True → (p5 ∨ (p5 → ((p5 → ((((p5 → True) ∨ p2) ∨ ((p5 → (p3 ∧ p3)) → p4)) → True)) → ((p3 → (p1 ∨ (p2 → False))) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_136528680777571032308403786944 : (((False → (p4 ∧ p1)) ∧ ((((p5 ∨ (((True ∧ (p1 ∧ p3)) → (False ∧ p5)) ∧ (p5 → p3))) ∨ p4) → p4) → p4)) ∨ ((p1 → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263556550637452864619548370629 : (True ∧ (((((((p5 → (p1 ∨ False)) ∨ False) ∧ (p2 ∨ p4)) ∧ ((p1 ∧ p3) → p5)) ∧ (p5 → p2)) → p4) ∨ ((p3 → p5) ∨ (False → True)))) := by
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
theorem thm_5_vars_640619969648609524043121262737 : (((((p1 ∨ p4) ∧ ((((p1 ∨ (False ∨ (((p4 → ((p5 ∨ True) ∧ p2)) → (True ∧ p2)) ∨ (True → True)))) ∧ p3) ∧ p1) → p3)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609692585814452442660118577852 : (((((p2 ∨ ((((p2 → (p1 → p1)) ∧ ((p4 → True) ∧ ((p2 ∨ (p2 → p2)) → ((p3 ∧ p3) → False)))) ∨ p1) ∨ p2)) ∨ True) ∨ p4) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_249077591706099953629830028623 : ((p4 ∨ p1) ∨ (((p3 ∨ p4) → p5) ∨ ((False ∨ ((((True ∧ p3) ∨ p1) ∨ p3) ∧ (False ∧ p3))) ∨ ((p5 ∧ ((False ∧ True) ∧ True)) → p3)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149466053089726382482806635414 : ((False ∧ ((False → (p4 ∨ False)) ∧ (p2 ∧ ((p1 ∨ p2) ∨ ((False → p4) ∧ (((p2 ∧ p3) ∨ p5) → p5)))))) ∨ ((p1 ∧ (p4 ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256395960587418663516798891569 : ((False ∨ p3) → (((((p2 → ((p4 ∨ (p1 ∧ (True ∧ p4))) ∨ (((p1 ∧ p5) ∧ p3) ∨ True))) → False) ∧ p5) → ((p2 → p5) → p1)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : (p2 → ((p4 ∨ (p1 ∧ (True ∧ p4))) ∨ (((p1 ∧ p5) ∧ p3) ∨ True))) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h8
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197101388769514179852453627404 : (((p4 ∧ (p5 → ((p3 ∨ p2) ∨ True))) ∨ p1) ∨ (p2 ∨ ((p4 → (p4 ∨ (p1 ∨ (p5 → (p2 ∨ (p4 → p3)))))) → (True ∨ (p4 → True))))) := by
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
theorem thm_5_vars_774000527517856704804275815047 : (((False ∨ (((p4 ∨ (p4 ∨ (p5 ∧ p2))) ∨ ((p4 ∨ (p2 → (((p2 ∧ p3) → False) ∨ False))) → ((p4 ∨ p1) ∧ True))) ∧ (p5 ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656879169743311875957561959491 : (((((p3 → ((False ∨ True) → p3)) ∧ ((False ∨ (p5 ∨ (((p5 → p4) ∨ ((p1 ∧ True) ∧ (True ∨ p2))) ∧ p2))) ∨ p5)) ∨ (p5 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49312773007056801407023467434 : (((p2 ∨ (((p1 ∨ ((p1 ∧ ((p1 → (p2 ∨ False)) ∧ False)) ∨ (True → p4))) → p4) → ((p4 ∨ p2) ∨ p3))) ∨ (p5 ∧ (True ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962606873029502644941781920045 : ((((True → p5) ∧ (((p1 ∧ False) ∧ (((p5 ∨ p4) ∧ p4) → ((p4 ∨ p1) → False))) → (False ∨ (((p4 ∨ p2) ∧ (p2 ∨ p4)) ∧ p4)))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



