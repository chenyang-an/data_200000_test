variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656287853550657181650718159588 : (((((p4 ∨ ((False ∧ (p3 ∨ p2)) ∨ (((True ∧ False) ∧ p3) ∧ p1))) ∧ (((p2 ∧ p1) → False) ∨ (p1 ∨ (p2 ∧ p1)))) ∨ (p5 → p5)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589456865612588167173460481091 : ((((((p1 ∧ (((((p5 → p3) ∧ ((((p1 ∨ p5) → p5) ∨ (p1 ∨ p4)) ∨ p3)) → (p5 ∧ p5)) ∧ p5) → p4)) ∨ p5) → p5) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208512062328760125345697993524 : (((p3 ∧ p2) → (p1 ∧ (p2 → p4))) → (((True ∨ p3) ∨ ((p5 ∧ p2) ∨ ((p4 ∨ (p5 ∧ p3)) ∨ p4))) → (p4 ∨ (True ∨ (p3 ∨ True))))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214749392900003445729857004089 : (((p4 ∧ p3) ∨ (p1 ∧ p5)) ∨ (((True ∧ ((False → p1) → (((True → ((True ∧ (p1 ∨ p3)) ∨ p5)) → p5) ∧ True))) ∨ p2) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322226894447473999836909662319 : (p5 ∨ (((p3 ∧ ((((p3 → ((p2 ∧ (((p2 ∨ p2) ∧ p5) ∧ (p2 → (p2 ∧ False)))) → (True ∨ p1))) ∧ True) ∨ p5) → p3)) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228787643757653148843177216063 : ((p3 ∨ (p5 ∧ p4)) ∨ (((p5 → p1) → p3) ∨ ((p2 ∧ p3) → (((p1 → (p5 ∧ p4)) ∨ p2) → (p2 → (False ∨ ((False ∨ p2) → True))))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657708185111699717384311339956 : (((((p3 → False) → (p4 ∨ (p3 ∨ (((((False ∨ p5) ∧ p5) → (p4 ∧ (p5 ∧ (p5 → p2)))) ∧ p5) → (False ∧ True))))) ∨ (p3 → True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_653570572211109157420051163291 : (((((((p3 ∧ (True ∧ (((p1 → (True ∧ (((p5 ∧ (False → True)) ∧ p3) → p5))) → p1) ∧ p5))) ∨ p4) ∧ True) ∧ False) ∨ (True ∨ p3)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_168439106376573832726246205246 : (((p3 ∨ p4) → (((p5 ∧ p5) → False) → ((True ∧ (p3 ∨ p4)) ∨ (p2 ∨ (p1 ∨ True))))) → (((p5 ∧ p3) ∨ p3) → ((p2 → False) ∨ p3))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232463951796783486329429509176 : ((True ∧ (p1 ∨ p3)) → (((p3 ∨ ((((p3 ∧ p4) → False) ∨ ((((p3 → p3) ∨ ((True → p4) ∧ True)) → p3) ∨ p3)) ∧ p1)) ∨ p1) ∨ False)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49509228821409682696281133223 : ((((p5 → ((((((p5 ∨ p4) → True) ∨ (p3 ∨ False)) → (p5 ∨ p4)) ∧ p5) ∨ ((False → p3) ∨ p2))) → p3) → ((p1 ∧ p5) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43809142975156026022308221362 : ((((p1 → (p2 → ((((True → (p1 → (p4 ∨ (False → (p1 ∨ False))))) ∧ (p4 ∧ False)) ∧ ((False ∨ p1) ∨ True)) ∨ p2))) → False) → False) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → (p2 → ((((True → (p1 → (p4 ∨ (False → (p1 ∨ False))))) ∧ (p4 ∧ False)) ∧ ((False ∨ p1) ∨ True)) ∨ p2))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604823826396736042133430882356 : ((((p1 → ((((True ∧ True) → ((p5 → (((False ∨ p5) → (p2 → False)) ∨ (p4 → (p3 → p5)))) ∧ p2)) → False) ∨ (p1 ∨ False))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117364910742321777482780562485 : ((False ∧ (p3 ∨ (False ∧ (p5 ∨ ((((p2 ∧ ((p4 → True) → (p5 ∨ p4))) → (((p5 ∧ p3) ∨ True) ∨ p3)) → p5) ∧ True))))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234009783603012476201236156244 : ((p5 ∨ (p3 ∨ p2)) → ((((((p1 → False) → (((p1 ∨ p2) ∨ p1) → True)) ∨ True) ∧ True) ∧ p2) → (False ∨ ((p4 ∧ (p1 → p2)) → True)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h22
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684586605568080275019608654950 : (((((((p4 → p2) ∨ p2) ∨ p4) → (p5 ∨ (p1 → ((((p4 ∧ p1) ∧ p3) ∧ p3) ∨ True)))) ∨ (p5 ∧ (p4 → ((False ∨ p1) ∨ p2)))) ∨ p1) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682930232869687567174411843814 : (((((p2 ∧ p5) ∨ ((p4 ∧ p3) → (p4 → (p5 → ((False ∧ p3) ∧ (False → (p5 → p5))))))) ∧ (p2 ∧ (p4 ∨ ((p5 ∨ p2) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231914869067157949653784644254 : (((False ∨ p1) → p5) → (((p5 → (p3 → p3)) → p3) ∨ ((p1 → ((p2 ∧ True) ∨ (p4 → ((p3 ∨ p1) ∨ ((True → False) ∧ p2))))) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110345903470838614546325879060 : ((p3 → (((p5 ∧ (((p4 ∨ (p4 ∧ False)) → False) ∧ (False ∧ (False ∧ ((True ∧ p4) → p5))))) ∨ (False → (p4 ∧ p4))) ∧ p3)) ∧ (False → False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66789798535236279867276843252 : ((True → (p1 ∨ (((p1 → (p3 ∧ ((p3 ∧ (p4 ∧ p5)) ∨ (((True ∨ ((p2 → p4) → False)) → p3) ∨ (p1 → False))))) → p4) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46196574032934259313209991230 : ((((p5 ∨ (((p1 ∨ (p2 ∨ ((p4 ∨ p3) ∧ (p4 → p1)))) → (((p2 ∨ False) ∨ p3) ∨ (p1 ∧ True))) → p1)) → p2) ∧ (p3 → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678006887633220943451631218731 : ((((((p4 ∧ ((p3 ∨ True) → p2)) ∧ ((p1 ∧ (p5 ∨ (p1 ∨ True))) ∨ p1)) ∧ (p1 → (False ∨ p3))) ∨ ((p4 ∨ (True ∧ p3)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230152884177821048449233232168 : (((p4 ∧ p3) ∧ p3) → (((p2 ∨ (True ∨ p1)) → (False ∨ ((True → (False ∨ False)) → (((((p4 ∧ p1) ∨ False) → p5) → p5) ∨ False)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h17 := h15 h16
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- False on the left can always be used.
        apply False.elim h19
    case inr h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h22 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h23 := h21 h22
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- False on the left can always be used.
        apply False.elim h24
      case inr h25 =>
        -- False on the left can always be used.
        apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68896936025033734622256626486 : ((p4 → (p4 ∧ (p1 ∨ (((p5 ∧ p5) ∨ ((p3 → (False ∧ p2)) ∨ p5)) ∧ (p3 → ((True ∧ (p2 → ((p4 ∨ p3) ∨ p4))) ∨ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118902181006311221900672894757 : ((True → (p5 ∨ ((((((((p3 ∨ p5) → (False → True)) ∧ (((p1 → True) ∨ p5) ∧ p3)) ∧ p5) ∨ p3) → p3) → p5) ∨ True))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113497031478683817942498299550 : (((((p1 ∧ True) ∧ (((p1 → (((p1 ∨ p1) ∨ (p3 ∧ p1)) → p4)) ∧ p2) → p3)) ∨ (p2 ∨ (p5 ∨ p1))) ∨ (p5 → True)) ∨ (p4 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51581398344467434486334331152 : (((p5 ∨ ((p4 → p2) → (p5 → (p1 → (((((p5 ∧ p2) → False) ∧ p3) → p1) ∨ False))))) → (p1 → ((False ∨ (p5 → p4)) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136159578295038134283334985472 : (((True ∨ ((False ∨ (True → p4)) ∨ (p1 ∧ True))) → ((((True → p3) → (p4 → True)) ∧ ((p1 ∧ p5) ∧ p4)) → False)) ∨ (True ∨ (p1 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_918887878302950953928310702412 : (((((((True → (True ∨ True)) ∨ p3) → (((True ∧ p4) → False) ∧ False)) → p4) ∧ ((p4 ∨ True) → (((p5 ∧ p3) ∨ (False → p4)) ∧ False))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p4 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158060341390903317213112897330 : (((p5 ∨ (p4 ∨ ((p3 ∧ p2) ∧ True))) ∨ (((p1 ∧ (p1 → ((False ∧ True) ∨ p5))) ∨ p3) ∨ p1)) ∨ ((((p1 → p1) → p5) ∨ p5) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h3
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247495251949616912949226010481 : ((False ∨ p3) ∨ (((False → False) → (False ∧ (p2 → p3))) → ((((((p5 ∨ (False ∨ False)) → True) ∨ True) → (p3 ∧ False)) ∧ p5) ∧ (p3 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (False → False) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h4
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : (False → False) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h9
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- False on the left can always be used.
    apply False.elim h12
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h13 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h14 : (False → False) := by
      -- Implications on the right can always be decomposed.
      intro h15
      -- False on the left can always be used.
      apply False.elim h15
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h16 := h1 h14
    -- We need to get the left conjuct of h16 based on <expert-advice>.
    let h17 := h16.left
    -- False on the left can always be used.
    apply False.elim h17
  case inr h18 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h19 : (False → False) := by
      -- Implications on the right can always be decomposed.
      intro h20
      -- False on the left can always be used.
      apply False.elim h20
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h21 := h1 h19
    -- We need to get the left conjuct of h21 based on <expert-advice>.
    let h22 := h21.left
    -- False on the left can always be used.
    apply False.elim h22
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h23 : (False → False) := by
    -- Implications on the right can always be decomposed.
    intro h24
    -- False on the left can always be used.
    apply False.elim h24
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h25 := h1 h23
  -- We need to get the left conjuct of h25 based on <expert-advice>.
  let h26 := h25.left
  -- False on the left can always be used.
  apply False.elim h26
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h27 : (False → False) := by
    -- Implications on the right can always be decomposed.
    intro h28
    -- False on the left can always be used.
    apply False.elim h28
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h29 := h1 h27
  -- We need to get the left conjuct of h29 based on <expert-advice>.
  let h30 := h29.left
  -- False on the left can always be used.
  apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111008552369350375314044333633 : (((((False ∨ (((((p3 ∧ p4) ∧ p2) ∧ p1) ∧ ((p4 ∨ p4) → (p2 ∨ False))) ∨ p2)) → p3) ∨ (True → (False ∨ p3))) ∧ p2) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249976149156171046412948554779 : ((True → p2) ∨ (((p5 → p3) → ((True ∨ p5) → ((((p1 ∧ p1) → p3) ∧ p5) → ((p4 ∧ p2) ∨ True)))) ∨ (False ∧ ((p2 ∧ p5) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
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
theorem thm_5_vars_138059919335818495076244307987 : ((True → (p5 ∧ ((((p3 → (p4 ∧ True)) → False) → p1) → (True → (p2 ∧ ((p4 → (p5 ∨ False)) ∨ (p1 → p1))))))) ∨ (p2 → (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135202558235952551772535074324 : (((((((p3 → (p4 ∧ (True ∨ (p5 ∨ p4)))) → (p3 ∧ p3)) ∨ p1) → (True ∨ False)) ∨ (True → p4)) → (p4 → False)) ∨ ((p2 ∧ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85137247879216992013864115413 : (((((p1 ∨ (False ∨ p4)) ∨ (True ∨ ((p5 → True) ∧ True))) ∧ (True ∧ True)) → ((((True ∨ p5) ∧ (p3 ∨ True)) → False) ∧ (p4 ∨ p3))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ (False ∨ p4)) ∨ (True ∨ ((p5 → True) ∧ True))) ∧ (True ∧ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((True ∨ p5) ∧ (p3 ∨ True)) := by
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
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192722878945038756329562153098 : (((((p1 → True) → False) → ((p2 ∨ p4) ∧ p2)) → False) → (p4 → (p2 ∨ ((True → p5) → ((((p2 → p2) ∨ p3) ∨ p5) → (p4 ∧ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p1 → True) → False) → ((p2 ∨ p4) ∧ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p1 → True) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h5
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h3
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787042092529150978921256385117 : (((p4 ∨ ((p3 ∧ True) ∨ (((p4 → (True ∨ False)) → (((p2 → False) ∨ ((p4 → (p1 ∧ p5)) → ((p4 → p3) → False))) ∧ True)) ∨ True))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598814166512596938991775180857 : (((((p3 ∧ True) ∧ ((True → p1) ∧ (((p4 → (((((p5 ∧ False) ∨ p3) → False) ∧ p5) ∨ ((True → p4) ∨ False))) ∧ False) ∧ p5))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113655486775904285488408018181 : ((((p3 ∧ ((p1 ∨ p2) ∧ (((p5 ∧ (p5 ∧ (p4 ∧ ((False ∨ (p5 ∨ True)) ∧ False)))) ∨ p3) → p5))) ∧ p1) → (p2 ∨ p5)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213774942828157096834691416359 : (((False ∧ (p2 ∧ p3)) ∨ p5) ∨ (((((((p4 ∨ p3) ∧ (p1 ∧ (p1 ∨ (p1 ∧ p1)))) ∧ p3) → p1) → (False ∧ False)) ∧ (p2 ∨ p2)) → p3)) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((((p4 ∨ p3) ∧ (p1 ∧ (p1 ∨ (p1 ∧ p1)))) ∧ p3) → p1) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h10.left
        let h13 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- One of the premise coincides with the conclusion.
          exact h17
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h10.left
        let h20 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h22 =>
          -- Conjunctions on the left can always be decomposed.
          let h23 := h22.left
          let h24 := h22.right
          -- One of the premise coincides with the conclusion.
          exact h24
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h25 := h2 h5
    -- We need to get the left conjuct of h25 based on <expert-advice>.
    let h26 := h25.left
    -- False on the left can always be used.
    apply False.elim h26
  case inr h27 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h28 : ((((p4 ∨ p3) ∧ (p1 ∧ (p1 ∨ (p1 ∧ p1)))) ∧ p3) → p1) := by
      -- Implications on the right can always be decomposed.
      intro h29
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- Conjunctions on the left can always be decomposed.
      let h32 := h30.left
      let h33 := h30.right
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h33.left
        let h36 := h33.right
        -- Disjunctions on the left can always be decomposed.
        cases h36
        case inl h37 =>
          -- One of the premise coincides with the conclusion.
          exact h37
        case inr h38 =>
          -- Conjunctions on the left can always be decomposed.
          let h39 := h38.left
          let h40 := h38.right
          -- One of the premise coincides with the conclusion.
          exact h40
      case inr h41 =>
        -- Conjunctions on the left can always be decomposed.
        let h42 := h33.left
        let h43 := h33.right
        -- Disjunctions on the left can always be decomposed.
        cases h43
        case inl h44 =>
          -- One of the premise coincides with the conclusion.
          exact h44
        case inr h45 =>
          -- Conjunctions on the left can always be decomposed.
          let h46 := h45.left
          let h47 := h45.right
          -- One of the premise coincides with the conclusion.
          exact h47
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h48 := h2 h28
    -- We need to get the left conjuct of h48 based on <expert-advice>.
    let h49 := h48.left
    -- False on the left can always be used.
    apply False.elim h49



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127938439866019467023204029784 : ((False → (True ∨ ((((((p1 ∧ True) → True) → p3) ∨ (((p1 → (p3 → p1)) ∨ (p4 → True)) → p3)) ∨ p2) → (True ∧ False)))) → (p3 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667417287119403172994506131827 : (((((p2 ∨ p5) → (p4 ∨ ((p5 → (((p3 ∨ (p1 ∧ p5)) ∨ p2) ∧ (False ∨ (p4 → True)))) ∧ (p2 ∧ p1)))) ∧ (p3 ∧ (True ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228737037587791049421301213898 : ((p2 ∨ (p3 → p4)) ∨ ((p5 ∧ (False ∨ True)) ∨ (p2 ∨ (((False ∨ (((p4 ∧ p1) ∧ (False ∨ p5)) → (p4 ∨ p5))) ∨ (p4 ∨ p3)) ∨ True)))) := by
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
theorem thm_5_vars_307324369488151809434606933017 : (p1 ∨ (p3 ∨ ((((p1 → (p5 ∨ (p5 → ((p2 → p5) → p4)))) → p3) ∨ p2) ∨ ((False → False) ∨ ((p1 → p2) ∨ ((False ∨ p2) ∧ False)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612554169011503112225959916222 : ((((((((p1 ∧ ((((p4 → p3) ∨ (p2 ∨ (True ∧ False))) → (False → p1)) ∨ (p2 ∨ False))) → p4) → p4) → p3) ∨ (p1 ∧ p1)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_149849237044873704275604117311 : ((p1 ∨ (p5 ∧ ((((p4 ∧ p2) ∨ (p4 → (p5 ∧ ((p3 → (p4 → True)) ∧ (p4 ∨ True))))) ∧ p1) → p3))) ∨ (((p4 → p5) → True) ∧ True)) := by
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
theorem thm_5_vars_250861328033515254997323195646 : ((p1 → p2) ∨ (p5 → ((((p3 → ((False → (p1 ∧ p2)) → (p3 → p3))) ∧ True) ∨ p5) → ((((p2 ∧ p2) → p3) → (p2 → p3)) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : (p2 ∧ p2) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h4
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : (p2 ∧ p2) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h4
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- One of the premise coincides with the conclusion.
    exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53630223618806706535014833237 : (((((p2 → (False → p4)) → p4) ∨ ((p2 → p1) → p3)) ∧ (p5 ∨ ((p2 → ((p3 ∧ p5) ∨ (True ∧ p4))) ∨ (p4 ∧ (p3 ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299321298426234056917602039277 : (False ∨ ((((False ∨ True) ∧ (True ∧ (p3 ∨ p5))) → (((p5 → p1) ∧ (((p1 ∧ ((p3 ∨ False) → (p4 ∨ p2))) → False) ∧ p3)) ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62141785507872468151232811430 : ((p2 ∧ (True → (((((((p1 ∧ (p2 ∧ p3)) ∧ p3) → p3) ∧ False) ∨ ((p2 ∨ (p3 ∨ p5)) ∧ True)) ∨ (True ∧ (p3 ∧ p3))) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173356127982096412321826736409 : ((p3 → ((True ∨ ((p2 → ((True ∧ p4) ∨ False)) → (p1 → p3))) → (p5 → p1))) ∨ (((((p1 → p3) ∨ False) ∨ p1) → True) ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66510749404551088703341031666 : ((True → (((((p4 → (False → ((True ∨ p5) → p4))) ∧ (True → (((p2 ∧ p4) ∧ p4) ∧ (p1 ∨ (True ∨ p4))))) ∨ p3) ∧ p2) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119554384314673786633263389728 : ((p5 → ((((p3 ∨ (p3 → p4)) ∧ ((True → p5) ∧ (p2 → (p1 → (False → p2))))) → p4) ∨ (True ∨ (p4 ∨ (p1 → False))))) ∨ (p5 ∧ p5)) := by
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
theorem thm_5_vars_206420004081951245452940519495 : ((p3 ∨ (p3 ∨ (p1 ∨ (p4 ∨ p2)))) ∨ (((((((p3 ∨ p1) ∧ p4) ∨ p5) ∨ (False → ((p1 ∨ p3) ∨ (p5 ∧ False)))) ∨ p2) → p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224476191238401339557952869758 : ((p1 → (p2 → True)) ∧ ((((p3 ∨ p3) → p5) ∨ ((p4 ∨ ((p3 → (p5 ∧ False)) ∧ p1)) → p3)) → ((p5 ∧ (True ∧ (p5 → False))) → p2))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h9 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h13 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h14 := h8 h13
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654533363303550852786559660451 : (((((p5 ∧ (((p3 ∧ ((False → p1) ∧ ((True ∧ p2) → (p5 ∨ p2)))) → ((p5 ∧ p2) ∧ (p4 ∧ p4))) ∧ p1)) ∨ True) ∨ (p1 → p3)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_599606905104907362568056144175 : (((((p5 ∨ p5) ∨ ((((True ∨ False) → (p3 → (p2 → p4))) ∧ ((True ∧ (True → p4)) ∧ p1)) → ((False ∨ (p1 → p3)) → False))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306012972052135582585382415873 : (p1 ∨ ((p3 ∧ (p3 ∨ (p4 ∧ p4))) ∨ ((False ∨ ((False ∨ p2) ∨ (p4 ∧ p4))) → ((p2 → (p5 → (False → (p1 ∨ True)))) → (p5 → p5))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755602773922334921719230427172 : (((p1 ∧ ((((((((p3 ∧ True) ∧ p4) ∧ (p3 ∨ ((p3 → (p3 ∧ p3)) ∨ p3))) ∧ True) ∧ (p1 → (p3 ∧ p2))) ∧ p5) → p1) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301373957104583226076141787909 : (False ∨ (((p3 ∧ (p5 → True)) → False) ∨ (((p2 ∨ (p2 ∨ (((((p1 ∧ p5) ∨ p1) → p4) ∨ p5) ∨ (p5 ∨ True)))) ∨ p5) ∧ (False → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64446627971093491517554861771 : ((p1 ∨ (((((p3 ∨ p2) ∨ ((p3 ∧ p1) → p2)) ∧ ((p3 ∨ p5) ∨ (p3 → ((p5 ∨ p3) ∧ (p1 ∨ p4))))) ∧ p3) → (p2 ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39110076154418980169656689436 : ((((p3 → p5) ∨ (((((True → ((True ∧ (True ∧ p1)) → (p1 ∧ (p2 → p4)))) ∧ p4) ∨ p5) → (False ∧ (p2 ∨ p1))) ∧ p2)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350050070411707229559168277405 : (p4 → (((False → (p2 → ((False ∧ (p4 ∨ ((p1 ∨ (p4 ∨ True)) ∧ (p2 ∧ False)))) ∧ ((p5 ∧ ((p1 → True) ∧ p4)) ∧ p1)))) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117259371597880017243942501129 : ((True ∧ (p4 → ((p1 → p1) → ((p3 → (p1 ∧ (p1 ∧ p4))) ∧ (p1 → ((p5 ∧ (p1 ∨ p3)) → (p4 → (p3 ∧ p1)))))))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351782337444861704883405221150 : (p4 → (((p1 ∧ (False ∧ (((p5 ∧ (p2 ∨ p3)) ∧ p1) ∨ p5))) ∨ p4) ∧ (((p5 ∧ (((p2 → p2) ∨ p4) → p5)) → (p1 → p2)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69195503387727776844190661360 : ((p5 → (((((p3 ∨ False) → p1) → ((p1 → True) ∨ p5)) → p4) ∧ ((p5 ∨ p1) → ((p4 ∨ (p1 ∧ (p3 ∨ True))) ∨ (p3 → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_399362539104479250554243715131 : ((((p2 → ((p4 ∨ (((((p2 ∨ True) → p4) ∨ (p4 → False)) ∧ p5) ∧ ((p3 ∨ ((p5 ∨ p1) → p4)) ∨ (False ∧ p4)))) ∨ True)) ∨ False) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54672910167697713587950694615 : ((((((p1 → (p1 → False)) → False) ∨ True) → False) → ((False ∧ (True ∧ (True → (p1 → ((((False → p1) ∨ p2) → p1) → p2))))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790815596160581502516196804354 : (((p5 ∨ (p1 → (True ∧ ((p2 → (((p3 ∨ p1) → p3) ∧ ((p5 → ((p1 → p1) ∨ (p4 ∧ ((p3 ∧ p2) ∨ False)))) ∨ p5))) ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59957767835091415665914113982 : (((True ∨ p4) → ((((p2 ∨ p5) ∨ (((True → (p1 → (p2 ∧ (p3 ∧ p4)))) → (False ∧ p3)) ∧ p3)) ∨ ((p1 ∧ False) ∧ p3)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165960738479559798880775609975 : (((True → p5) ∧ ((p1 ∨ False) ∧ (p5 ∧ ((True ∧ (p1 ∨ (p2 ∧ (p5 ∨ p3)))) ∧ p4)))) ∨ (p2 ∨ (True ∧ (True ∨ (p2 ∨ (p1 → True)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168288383792057272223118626286 : (((p5 ∧ p2) ∧ ((((True → p2) ∧ (True → False)) ∧ ((p4 → True) ∨ (True ∧ p2))) ∧ p1)) → ((p3 ∧ (p4 ∧ (p2 → p4))) ∧ (p3 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h12 =>
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h14 := h11 h13
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h18 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h19 := h11 h18
    -- False on the left can always be used.
    apply False.elim h19
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h20.left
  let h23 := h20.right
  -- Conjunctions on the left can always be decomposed.
  let h24 := h21.left
  let h25 := h21.right
  -- Conjunctions on the left can always be decomposed.
  let h26 := h24.left
  let h27 := h24.right
  -- Conjunctions on the left can always be decomposed.
  let h28 := h26.left
  let h29 := h26.right
  -- Disjunctions on the left can always be decomposed.
  cases h27
  case inl h30 =>
    -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
    have h31 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h29, we can now drive its conclusion.
    let h32 := h29 h31
    -- False on the left can always be used.
    apply False.elim h32
  case inr h33 =>
    -- Conjunctions on the left can always be decomposed.
    let h34 := h33.left
    let h35 := h33.right
    -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
    have h36 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h29, we can now drive its conclusion.
    let h37 := h29 h36
    -- False on the left can always be used.
    apply False.elim h37
  -- Implications on the right can always be decomposed.
  intro h38
  -- Conjunctions on the left can always be decomposed.
  let h39 := h1.left
  let h40 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h41 := h39.left
  let h42 := h39.right
  -- Conjunctions on the left can always be decomposed.
  let h43 := h40.left
  let h44 := h40.right
  -- Conjunctions on the left can always be decomposed.
  let h45 := h43.left
  let h46 := h43.right
  -- Conjunctions on the left can always be decomposed.
  let h47 := h45.left
  let h48 := h45.right
  -- Disjunctions on the left can always be decomposed.
  cases h46
  case inl h49 =>
    -- We want to use the implication h48 based on <expert-advice>. So we show its premise.
    have h50 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h48, we can now drive its conclusion.
    let h51 := h48 h50
    -- False on the left can always be used.
    apply False.elim h51
  case inr h52 =>
    -- Conjunctions on the left can always be decomposed.
    let h53 := h52.left
    let h54 := h52.right
    -- We want to use the implication h48 based on <expert-advice>. So we show its premise.
    have h55 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h48, we can now drive its conclusion.
    let h56 := h48 h55
    -- False on the left can always be used.
    apply False.elim h56
  -- Implications on the right can always be decomposed.
  intro h57
  -- Conjunctions on the left can always be decomposed.
  let h58 := h1.left
  let h59 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h60 := h58.left
  let h61 := h58.right
  -- Conjunctions on the left can always be decomposed.
  let h62 := h59.left
  let h63 := h59.right
  -- Conjunctions on the left can always be decomposed.
  let h64 := h62.left
  let h65 := h62.right
  -- Conjunctions on the left can always be decomposed.
  let h66 := h64.left
  let h67 := h64.right
  -- Disjunctions on the left can always be decomposed.
  cases h65
  case inl h68 =>
    -- We want to use the implication h67 based on <expert-advice>. So we show its premise.
    have h69 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h67, we can now drive its conclusion.
    let h70 := h67 h69
    -- False on the left can always be used.
    apply False.elim h70
  case inr h71 =>
    -- Conjunctions on the left can always be decomposed.
    let h72 := h71.left
    let h73 := h71.right
    -- We want to use the implication h67 based on <expert-advice>. So we show its premise.
    have h74 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h67, we can now drive its conclusion.
    let h75 := h67 h74
    -- False on the left can always be used.
    apply False.elim h75



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116618413590031336443987541051 : (((False → p1) ∧ ((p4 ∨ (p5 ∧ p5)) ∨ (p3 ∨ (((((p5 ∧ p3) ∧ True) ∨ ((p2 ∨ p1) ∨ (True ∧ p4))) ∨ True) → p2)))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208412415739052986627702717410 : (((p1 ∨ p2) ∨ (p2 ∧ (p5 → p5))) → (p1 ∨ (((((p1 → False) ∧ ((p3 ∧ ((p4 → p3) ∨ False)) ∨ p4)) ∨ True) → (True → False)) → p4))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h6 : (((p1 → False) ∧ ((p3 ∧ ((p4 → p3) ∨ False)) ∨ p4)) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h7 := h5 h6
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h9 := h7 h8
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : (((p1 → False) ∧ ((p3 ∧ ((p4 → p3) ∨ False)) ∨ p4)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h15 := h13 h14
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h17 := h15 h16
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688664907070661288722325083538 : ((((True → ((False ∧ (p4 ∧ p1)) ∨ ((False ∨ p3) ∧ ((True → p1) ∧ (True → p4))))) ∧ (p2 ∧ ((True → (p3 → (p2 ∧ p2))) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_914286892661738959818914236092 : ((((((p3 ∨ (p1 → False)) ∧ (((False ∨ (p1 ∨ p5)) ∨ p1) ∧ p2)) ∨ (False ∧ p3)) ∧ (p3 → ((((p2 → p4) ∨ p5) ∧ False) ∧ p2))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h14 : p3 := by
              -- One of the premise coincides with the conclusion.
              exact h7
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h15 := h3 h14
            -- We need to get the left conjuct of h15 based on <expert-advice>.
            let h16 := h15.left
            -- We need to get the right conjuct of h16 based on <expert-advice>.
            let h17 := h16.right
            -- False on the left can always be used.
            apply False.elim h17
          case inr h18 =>
            -- One of the premise coincides with the conclusion.
            exact h18
      case inr h19 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h20 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h21 := h3 h20
        -- We need to get the left conjuct of h21 based on <expert-advice>.
        let h22 := h21.left
        -- We need to get the right conjuct of h22 based on <expert-advice>.
        let h23 := h22.right
        -- False on the left can always be used.
        apply False.elim h23
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h6.left
      let h26 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- False on the left can always be used.
          apply False.elim h28
        case inr h29 =>
          -- Disjunctions on the left can always be decomposed.
          cases h29
          case inl h30 =>
            -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
            have h31 : p1 := by
              -- One of the premise coincides with the conclusion.
              exact h30
            -- We have shown the premise of h24, we can now drive its conclusion.
            let h32 := h24 h31
            -- False on the left can always be used.
            apply False.elim h32
          case inr h33 =>
            -- One of the premise coincides with the conclusion.
            exact h33
      case inr h34 =>
        -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
        have h35 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h34
        -- We have shown the premise of h24, we can now drive its conclusion.
        let h36 := h24 h35
        -- False on the left can always be used.
        apply False.elim h36
  case inr h37 =>
    -- Conjunctions on the left can always be decomposed.
    let h38 := h37.left
    let h39 := h37.right
    -- False on the left can always be used.
    apply False.elim h38
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183800575083901962156258655168 : (((((True ∧ (p4 ∧ True)) ∧ (False ∨ (False ∨ p1))) ∨ p1) ∧ False) ∨ (((p5 ∨ ((p5 ∨ (((p5 → False) → p3) ∧ p2)) ∨ False)) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196980282488097101358312750833 : (((((p2 ∨ (p4 ∨ False)) → p3) → p3) ∨ p2) ∨ ((False ∨ ((((p4 → ((p2 → p4) ∨ p2)) ∨ p3) ∧ p2) → (p1 → p2))) ∨ (True → p1))) := by
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
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734413104889062245656942372846 : ((((False ∨ p5) ∧ ((((((True ∨ True) ∧ (p2 → (True ∨ (p2 → True)))) → (True → (p3 → p1))) → (p2 ∧ (True → p1))) ∨ False) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357176139663871336069570575583 : (p5 → ((False ∨ p5) ∧ (((((p4 ∧ p5) ∨ p3) → ((True ∨ p2) ∨ (p4 → p4))) → (p3 ∨ ((True → p4) ∨ True))) ∧ (p2 ∨ (True ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724740135452126291507875069841 : ((((p3 ∨ (True ∨ p2)) ∧ (((True → p4) ∧ ((p2 → ((((p3 ∨ (False ∨ p3)) ∧ (False → (p4 ∨ p2))) ∧ p2) ∨ False)) → p4)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736829483281876818383416731578 : ((((p2 → p3) ∧ ((((False ∧ p4) ∨ False) → False) → (((False ∨ p4) ∧ p1) ∧ (p3 ∨ ((p4 ∨ p1) → (p1 → (False → (p2 ∨ True)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113507386224027611615975819686 : ((((((p5 ∧ (p5 → ((p4 → p5) ∧ (p3 ∨ (p5 ∨ False))))) → p4) ∧ p4) → (False ∧ ((p2 → p1) → False))) ∨ (p5 ∧ p4)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140254581442971650977718055544 : (((((((p4 → p4) ∧ False) → p5) ∨ (p1 → ((p5 ∧ (p4 → p2)) ∧ (p1 ∧ p2)))) ∧ p5) ∧ (p5 → (p2 ∧ False))) → (p1 ∧ (p4 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h18 =>
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h19 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h20 := h15 h19
    -- We need to get the right conjuct of h20 based on <expert-advice>.
    let h21 := h20.right
    -- False on the left can always be used.
    apply False.elim h21
  case inr h22 =>
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h23 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h24 := h15 h23
    -- We need to get the right conjuct of h24 based on <expert-advice>.
    let h25 := h24.right
    -- False on the left can always be used.
    apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184303861343911678609872257976 : (((((True ∨ p3) ∧ p3) → (p2 ∧ ((p4 ∨ True) ∨ p2))) → False) ∨ (((p5 ∨ True) → False) ∨ ((((p5 ∨ (True ∧ p1)) → True) ∧ p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247784350074805439473680081100 : ((p1 ∨ p1) ∨ ((p3 ∨ (((p2 ∧ p2) ∧ False) ∨ (p4 → (p4 ∨ (((p4 ∧ True) ∨ (False ∨ p3)) → ((p2 ∨ p1) → True)))))) ∨ (False ∧ p1))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300064588257540877079182428250 : (False ∨ ((((p2 ∨ ((p4 → True) ∧ (False ∨ (False ∧ ((p2 ∨ ((p3 ∨ p3) ∧ True)) → p2))))) ∧ (p4 ∨ (False ∧ p1))) ∨ p5) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783915028914202906252631615180 : (((p3 ∨ ((p4 ∧ (p1 → p5)) ∨ ((((((p1 → p2) → p3) ∨ (p5 ∧ p1)) ∧ False) ∨ ((True → (True → (p2 ∧ p1))) ∧ p3)) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588679512346749315120247106775 : (((((p2 ∧ (((((p4 → ((False ∨ p3) ∨ p3)) → (((p1 ∨ p5) ∧ False) → ((p2 ∨ p2) ∧ p3))) ∧ True) ∧ p5) ∧ False)) ∨ p5) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135372453263638493901134162271 : ((((True → (p4 ∨ (False ∨ (True ∧ (p3 → (((p1 ∧ (p5 ∨ True)) ∨ p2) → p4)))))) ∧ True) ∨ ((p4 ∨ p3) → p4)) ∨ (p4 → (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674806948526610105613132815523 : ((((p4 → (p5 ∨ (((p4 ∧ p4) → ((False ∨ p2) → ((p3 ∨ (p5 → (p4 ∧ (True → p4)))) ∨ p3))) → p1))) → (p3 ∧ (p2 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205505993413812145214594093815 : (((p3 ∧ p5) ∧ (p5 ∧ (p4 ∨ p5))) ∨ (((True ∧ (((p4 ∧ p1) → (p3 ∧ p3)) ∧ p2)) → ((p1 → ((False → p2) ∨ False)) ∨ p3)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59474339377886011738379419542 : (((p1 → p2) ∨ (((p1 ∧ p2) → (((False ∧ ((p1 → p5) ∧ p5)) → p5) → (((p4 ∨ p2) ∨ p4) ∧ ((p3 → p4) ∧ p3)))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111693420371422754102833945455 : ((((((((((((p5 → p4) → (p1 → p2)) ∧ p3) ∨ p4) → p2) ∧ p4) ∨ (p1 → p5)) ∧ (True ∨ False)) → p1) → p3) ∨ p3) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113697757915652330144167494547 : ((((True ∧ ((((p2 ∧ p2) → ((p1 ∨ ((p5 ∧ p3) → p4)) → p3)) → (p4 ∧ (False ∨ False))) ∨ True)) → False) → (False ∨ p4)) ∨ (p1 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∧ ((((p2 ∧ p2) → ((p1 ∨ ((p5 ∧ p3) → p4)) → p3)) → (p4 ∧ (False ∨ False))) ∨ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661435552549972559977904952974 : ((((((((p5 ∨ ((p1 ∧ p2) ∧ (((False → p1) ∧ (p2 ∧ p2)) ∧ True))) ∨ p5) ∨ p4) ∨ p5) ∧ (False → (True ∨ True))) → (False ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225287890877978985711291102509 : (((False ∨ True) ∧ p1) ∨ (True → ((((p1 → (p4 → (p3 ∧ (True → False)))) → p3) ∨ p1) → (p2 ∨ (p2 → (((p3 ∨ p3) ∨ True) ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234857375235884661075923627033 : ((p5 → (False → False)) → (((p5 ∧ (p5 ∧ p3)) → p1) → (((((p1 ∨ (p1 ∧ p3)) ∨ p4) → p1) ∨ (((False ∧ True) → p5) ∨ p2)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115254116295122777941221762546 : (((((p1 ∨ p5) ∧ p4) ∧ ((p3 ∧ (True ∧ p2)) ∨ p5)) ∨ (p5 ∧ (True ∨ (((False ∨ p5) ∨ (p3 ∨ (p1 ∧ p2))) ∧ p3)))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



