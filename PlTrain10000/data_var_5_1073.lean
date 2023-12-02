variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217759050492000063543655491830 : (((p4 ∧ (True → True)) → True) → ((False → p5) ∧ ((((((((p4 ∨ p3) ∧ p2) ∨ p4) → ((p1 → True) ∧ p1)) ∨ p3) ∨ p1) ∧ False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157555464113707448602655019871 : (((((False ∧ ((True ∧ (True ∨ p5)) ∨ (False ∨ p5))) → (p1 ∧ p3)) → (p3 ∧ p3)) → (p2 ∧ p5)) ∨ (((p2 → p4) ∨ (True ∧ p5)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54660952254105484279576270503 : ((((p1 ∧ (p5 ∨ ((p3 ∧ False) → p4))) ∨ p1) → ((p3 ∨ ((p3 → p1) → (p3 ∧ (False → p1)))) → ((p3 ∧ p3) ∨ (p4 → p4)))) ∨ p4) := by
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
    cases h1
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h3
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h3
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197939804207056561053481840169 : (((False ∧ False) ∧ ((p1 ∧ p5) ∨ (True ∧ p3))) ∨ (((p2 ∨ p4) → ((p3 → p3) → (p3 → ((((p3 ∨ p3) ∧ True) → True) ∨ p2)))) ∨ False)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208630937131614178275769201282 : ((True ∧ ((p2 ∧ (p3 → p2)) → p3)) → (True ∧ (((p3 ∧ p4) ∨ p2) ∨ (p3 → (((False ∧ p2) ∨ False) ∨ ((p2 ∧ (p1 ∨ p2)) → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351537504932655625045308857318 : (p4 → (((p2 ∧ (True → p3)) ∨ ((p2 ∧ (((p3 ∨ p5) ∧ p2) ∨ p1)) ∧ ((p5 ∨ p2) ∨ True))) ∨ (False → ((p4 → (False → p3)) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116261624870685145733824841756 : (((p1 ∧ (p2 → p5)) ∨ ((p5 → (((((((p4 ∨ p5) ∧ p4) ∧ (p2 ∧ p1)) ∧ p3) → (p3 ∧ False)) ∧ p2) ∨ p3)) ∧ p3)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184095072875345518176618474841 : (((((p1 → True) ∨ p2) → (p1 → ((p5 ∨ True) → p2))) ∨ p1) ∨ ((p1 → p3) → ((p5 ∧ p3) → ((p4 ∨ True) ∨ ((p3 ∧ p2) ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326871678389836456097770412908 : (True → ((((False ∨ ((((p2 ∨ p2) → (p5 ∨ (((p5 ∨ p1) ∨ (p5 ∧ False)) ∧ False))) ∨ True) ∨ (True ∧ p4))) ∨ (False ∧ True)) ∨ True) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112210265700089401967760289162 : (((False ∨ ((p4 ∨ (((p4 ∨ (((p1 ∨ p3) ∧ p2) ∧ (p1 → False))) ∨ p3) → (p4 ∨ p5))) → ((p4 ∨ p1) → p2))) ∨ p1) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42305848790122998146979024410 : (((p2 ∧ (((((p5 ∨ ((p3 ∧ True) → (True → p1))) → p4) → (p1 ∧ p2)) → (True → p3)) → ((p5 ∨ p2) → (p4 → p4)))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110528742506157838679374696614 : ((p4 → ((((p4 ∨ p2) ∧ True) ∧ p1) → ((((p1 ∨ True) ∧ p3) ∨ ((p5 → (p4 → p2)) ∧ p2)) ∨ (p2 ∨ (False ∨ True))))) ∧ (True → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606664339311115975216005388045 : (((((((p3 ∨ (False ∨ (p2 ∨ ((True → p4) ∧ (p5 ∨ (p5 ∨ (p1 → ((p1 → p4) → True)))))))) ∨ p1) ∧ (p2 → True)) ∧ p5) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_314022985913373768155748769581 : (p3 ∨ ((p4 ∨ ((((p3 → p4) → False) → ((p5 ∧ ((p2 → (p4 ∨ p3)) → p3)) ∧ ((p1 ∨ p1) ∧ p1))) ∨ (p5 ∨ p2))) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702991034876818376380691479907 : ((((((p3 → p5) ∨ p2) → ((p5 ∨ p3) ∧ (p4 ∨ p4))) ∨ (p2 → (((p4 ∧ (True ∧ (False → p5))) ∨ (p4 ∧ p5)) ∨ (p2 ∨ False)))) ∨ p1) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67328716247721479840152148943 : ((p1 → ((((p1 ∨ (True ∨ ((p5 ∨ p1) ∨ ((p2 ∨ p4) ∧ (((p5 → p5) ∧ (False ∨ (p2 ∨ p3))) ∧ True))))) ∧ p4) → p2) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245304926129003460134149036190 : ((p2 ∧ p2) ∨ ((p4 ∨ ((False ∨ True) ∨ (p5 ∧ (((p3 → p2) ∨ p3) ∨ False)))) → ((p2 → (False ∨ False)) ∨ ((True ∧ (p5 ∨ p2)) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187364584881683400085657951397 : ((p3 ∧ (((p3 ∨ p3) → ((p3 ∨ p5) ∧ True)) ∨ (p2 → p3))) → ((True → ((p4 → ((p3 → p5) → ((p5 ∨ False) ∨ p1))) ∨ p2)) ∨ p5)) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h15 := h13 h14
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68497237479815117773397769185 : ((p3 → (p2 ∨ ((((True → False) ∧ ((p2 → p1) ∧ ((p4 → (p5 ∨ p1)) → p4))) → ((False → p5) → False)) ∧ ((p5 → True) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213359067125298943598283198175 : (((p4 ∧ (p1 ∨ p1)) ∧ True) ∨ ((p2 ∧ ((False ∨ True) ∧ ((True → (p5 → (p3 → ((False ∨ ((p2 → p3) ∧ p3)) ∨ True)))) → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336160195493093530904123038591 : (p1 → ((((((p5 ∧ (True ∨ (p3 ∧ p2))) ∧ ((p4 ∨ ((p3 ∧ p4) ∧ p4)) ∨ p3)) ∨ True) ∧ (p5 ∨ ((True ∨ p4) ∧ p5))) → False) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114922007848491504097075781569 : ((((p2 ∧ (p3 → ((p3 → p1) ∧ ((p1 ∨ p2) → (True → p4))))) → p2) → (((p3 → p2) ∧ ((p5 ∨ p3) ∧ p2)) ∧ p2)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303930046437030801086023964617 : (p1 ∨ ((((p3 ∧ (p2 ∧ (p1 ∨ p4))) ∧ (p4 → True)) ∨ (False ∨ (p3 ∨ (p5 ∨ ((p5 ∧ ((p5 ∧ (False ∨ p5)) ∧ p5)) ∨ p3))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173083455176540812933839041400 : ((p1 ∨ ((p4 → ((p3 ∨ p5) → ((False ∧ p2) ∨ ((p1 ∧ False) ∧ True)))) → p2)) ∨ ((((p3 → p5) → p1) → True) ∨ (True ∧ (p3 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799873520462702389611802720987 : (((p1 → (p5 → ((((((p4 ∨ False) ∨ p1) → p4) ∨ (((True ∧ False) → p2) ∧ p5)) ∧ (((p4 ∨ (p2 ∧ p5)) ∨ p2) → p4)) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174373175023252410237327707406 : ((((p1 → (p3 → ((True → p2) ∨ p1))) ∧ p4) ∧ (((p1 → p5) ∨ True) → p3)) → ((((p4 → (False ∨ False)) ∧ p4) ∨ (False ∧ p2)) → False)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h10 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h10
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51097069578697185840793117415 : ((((((p1 ∨ p5) ∧ ((True → p5) → True)) ∨ ((False ∧ p2) ∧ (p4 ∨ (p5 ∨ p1)))) ∧ p2) ∨ (((p2 ∧ (p3 ∨ p3)) → p5) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136744988577197805157309317233 : (((p1 ∨ True) ∧ ((p5 → (p3 ∨ (p1 ∨ False))) ∨ ((False ∨ ((((True ∨ p2) ∨ p5) ∨ p5) → (p1 ∨ True))) ∨ p1))) ∨ ((p2 ∨ p3) → p4)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h5 =>
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791961205496586279852891195863 : (((True → ((p2 → ((((p2 ∨ p1) ∨ ((True ∨ p3) → (p4 ∨ False))) ∧ p5) → (p3 ∨ (p4 ∨ ((True → True) ∨ p3))))) ∨ (False ∧ True))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119392414385162438309596312725 : ((p4 → ((((True → p5) ∨ (((p5 → p1) ∨ True) → (p3 ∧ p1))) → (((p2 ∧ False) ∧ (False ∧ (p3 ∨ p1))) ∧ p5)) ∧ p1)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262284831106522428933456822998 : (True ∧ ((((((p4 ∨ p5) ∨ ((p3 ∨ True) → ((False → p2) ∧ False))) → p1) → (p5 ∧ p5)) ∨ ((p4 ∧ p3) ∨ (False → (False ∨ p3)))) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301890082146528116208871862737 : (False ∨ ((True ∧ p4) → (((False ∨ (True ∧ p1)) ∧ ((p5 ∨ True) ∨ True)) ∨ (((p4 ∨ p2) → ((p3 ∨ True) ∧ (p4 ∧ True))) ∨ (p4 → p1))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_467735561101122303485156892714 : (((((p3 → ((p2 ∨ True) ∨ True)) → ((True → p2) ∨ (p4 ∨ (False ∨ p5)))) ∨ (((True ∧ p1) → ((True ∧ False) ∨ (p2 → p2))) ∧ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624669783311323512847448542885 : ((((p4 ∨ (False ∧ (((True ∧ (False ∨ False)) → (p4 ∧ p3)) → (p2 ∨ (p2 ∧ ((p1 → p2) → ((p3 ∧ (p4 → True)) ∧ p5))))))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626206530038366761295902193775 : ((((p3 → (((((False → (True ∧ p1)) ∧ (((p5 → p4) → False) → True)) ∧ p5) → (((p1 ∧ p2) ∧ p4) ∧ False)) ∨ (p3 ∨ p3))) ∨ p5) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684785166566565783390972006952 : (((((p5 ∨ p2) ∨ ((False ∨ (((p5 ∨ ((True → p4) ∧ (p1 ∨ False))) ∨ p5) ∨ p1)) ∧ p2)) ∨ (False → (True ∧ (False → (p5 ∧ True))))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202537100374649143836837532617 : (((False ∧ (False → True)) ∨ (p4 → True)) ∧ ((p3 ∨ (((False ∧ True) ∨ ((p1 → ((p1 ∨ (p5 → p2)) ∧ (True ∧ p5))) ∨ p1)) ∨ True)) ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_382738171106800814132830874550 : ((((((p1 ∧ (p3 → p5)) → (p3 ∨ ((True ∨ ((((True ∧ False) ∧ (p2 ∨ ((p5 ∨ p3) ∨ p5))) → True) ∨ p1)) ∧ p2))) ∨ False) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_318882011301349292228837362226 : (p4 ∨ (((p3 ∨ ((p2 ∨ p3) ∧ p3)) ∨ (True ∨ ((p1 → (((p5 ∨ p3) → p3) ∧ p4)) ∨ (p4 → (p2 → True))))) ∨ (True → (p2 ∨ p2)))) := by
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
theorem thm_5_vars_55119512013151665499660458110 : (((((p5 → (p3 ∨ p1)) → p1) ∧ p2) ∨ (p5 ∨ (((False ∧ p3) → ((True → (False ∨ (((True → True) ∨ False) ∧ p5))) → p2)) ∨ True))) ∨ p3) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151661527616450245308755484794 : (((((p2 → ((True → p5) ∧ p5)) ∧ p1) → (((p1 ∨ (p4 ∧ p5)) ∧ p2) ∧ p5)) ∧ ((p1 ∨ True) → p2)) → (((False ∨ p4) ∧ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p1 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148231092250359638783393323017 : ((((p3 ∧ ((p5 → p3) ∨ (p5 ∨ ((True ∨ (p3 ∨ (False → p4))) ∨ False)))) → p2) ∨ (p5 ∨ (p5 ∨ True))) ∨ (False ∨ (p1 ∧ (True → p5)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606310281028074640135117016409 : (((((((p4 ∨ (False ∧ (((p1 → p1) ∨ ((True → (p3 ∧ (((p3 → p4) ∨ p1) ∧ p4))) ∧ p4)) ∨ p2))) ∧ p4) ∨ p5) ∧ False) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192281135855551843866442865534 : ((((p5 → p2) ∧ ((p2 → (True ∧ True)) ∨ p5)) ∧ p2) → ((p4 ∧ (p4 ∧ (((((False ∧ p4) ∨ (p1 → False)) ∧ False) → p4) ∧ p1))) ∨ p2)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1542679538122982927254115627 : ((False ∧ (True ∧ (((p3 ∧ p4) ∧ ((p2 ∨ True) ∧ (p2 ∧ ((((False → (True ∧ p3)) ∧ p1) ∧ p3) ∨ p5)))) ∧ False))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119566946946708901505470578441 : ((p5 → (((p1 ∨ p2) ∧ ((p2 ∨ (True → p3)) → False)) ∨ ((True → (p2 ∨ p5)) ∧ (False → (((p3 ∨ p1) ∧ p5) → True))))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118612243016954055864858571373 : ((p4 ∨ (((p2 ∧ ((((p5 → (p2 → (p2 ∧ p3))) ∨ p3) ∧ p2) ∨ False)) → p5) ∧ (p2 → ((p1 ∧ (p4 ∨ p2)) → p4)))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61579943797294556263092718444 : ((p1 ∧ ((False ∨ ((p1 ∨ p5) ∨ p1)) ∨ (True ∨ (p1 ∧ ((p3 ∨ p5) → (p3 ∧ (False ∧ ((p4 → (p4 ∨ (p4 ∧ p4))) → p1)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64718376563439754909491504004 : ((p1 ∨ (p3 → (False ∧ (False ∧ (p5 ∧ (((p2 ∨ (p4 ∨ (p2 ∨ ((p2 → p5) → (((True → p5) → p3) ∨ p4))))) → p2) ∧ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40439232312542598634798025152 : (((((((p2 ∨ p5) ∨ False) ∧ (p3 ∧ (p2 → p3))) ∧ ((False ∧ (p2 ∧ p3)) ∧ (False ∨ (p5 ∧ ((p4 ∨ p3) → False))))) ∨ p1) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41356065784278108974508437872 : ((((((p2 ∧ p1) ∨ (((p1 ∨ p2) → p1) → ((p4 → (p2 ∧ p4)) ∧ p5))) ∧ True) → ((p5 → (p3 ∨ p3)) ∧ (False ∧ False))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208867040348644646822608751741 : ((p4 ∧ ((p5 → (False → p1)) → p4)) → ((((p1 ∧ p1) ∨ ((((p5 → (p5 ∨ p3)) → p2) → ((p2 ∨ p4) → False)) ∨ True)) ∨ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663928937075886664863297750364 : ((((p4 ∧ ((p4 ∧ (((p2 ∨ True) ∧ p4) → (((False → ((p3 → False) ∨ p5)) → p1) → p4))) ∧ ((p2 ∨ p1) ∨ p5))) → (p1 ∨ p4)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  cases h5
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48996238106109571849082766877 : ((((p1 ∨ (((((p5 ∧ p1) ∧ False) → (p5 → (p5 → True))) ∨ True) → ((p5 ∨ (p4 ∨ p1)) ∧ p1))) ∨ p3) ∨ (p2 → (True ∧ p2))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214287866637899216991464310675 : (((p4 ∧ (False → True)) → False) ∨ (((p1 ∨ (((p5 ∧ p5) ∨ p4) → (((((p2 ∧ p1) → p5) ∨ p1) → (True ∨ p1)) ∧ True))) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172543663667812119517489643043 : ((((p3 → p3) ∧ p5) ∨ (p2 ∧ (p1 ∧ (p5 ∨ (((p1 → p5) → False) ∨ p1))))) ∨ (((p4 ∧ (True ∨ p1)) ∨ (p1 ∨ (True ∨ False))) ∨ p5)) := by
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
theorem thm_5_vars_324946642292638907998801456597 : (p5 ∨ ((p3 ∨ p1) ∨ ((p5 → ((p3 ∧ p3) ∨ (p4 ∨ ((p5 ∨ (True → False)) ∨ p3)))) ∨ (p2 ∧ ((((False ∨ p4) ∧ True) → p2) ∨ p1))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179786151872161336255316425187 : (((((True ∨ False) ∨ True) ∨ (((p1 → (False ∨ p1)) → p3) ∨ p2)) ∧ p2) → ((((p1 → p4) ∧ False) ∧ p4) ∨ (((True ∨ False) ∨ p1) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
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
            -- False on the left can always be used.
            apply False.elim h10
        case inr h11 =>
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h17 =>
          -- False on the left can always be used.
          apply False.elim h17
      case inr h18 =>
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h24 =>
          -- False on the left can always be used.
          apply False.elim h24
      case inr h25 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h26 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h27
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h29 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h30 =>
          -- False on the left can always be used.
          apply False.elim h30
      case inr h31 =>
        -- One of the premise coincides with the conclusion.
        exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249611431668896796729931073746 : ((p5 ∨ p3) ∨ (((False ∨ ((False ∨ (p1 ∨ p5)) ∧ (p4 ∧ ((((p2 ∧ False) ∧ False) ∨ p5) ∨ p2)))) ∨ p3) ∨ (False → (p2 ∧ (p4 → p1))))) := by
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
theorem thm_5_vars_55028061233337839995692696660 : (((p2 ∧ ((p3 ∨ (True → p5)) ∨ p4)) ∧ ((p4 ∧ p1) ∧ (p2 ∨ (p2 → (((((True ∨ p5) ∧ False) ∧ p1) ∨ (False ∧ p3)) → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193523275548368301489290891575 : (((p3 → p1) ∨ (((p2 ∧ True) ∨ p4) → (p4 ∧ p4))) → (((p3 ∨ (False → p1)) ∧ ((((True ∨ p3) ∧ p1) ∧ False) ∧ p2)) ∨ (True ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232452919663558649726631906011 : ((True ∧ (True ∨ p3)) → ((((p2 ∧ (((p1 ∨ p1) ∨ (True ∨ (False → p1))) → False)) ∨ ((True ∧ p5) → p5)) ∨ p1) ∨ (p1 ∧ (True ∨ p2)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_17923584840491009363467802718 : (((((((p1 → True) ∨ True) → p2) ∧ ((p1 ∧ (((p4 → False) ∨ p4) ∨ p3)) → p2)) → (p4 ∨ p4)) ∨ ((False ∧ (p2 → True)) ∨ True)) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642998162236173684963349562697 : ((((p2 ∧ ((False → p3) ∧ ((((True ∧ p2) ∧ p5) ∨ ((((p2 ∨ (p5 → p2)) ∧ p1) ∨ (False ∧ p2)) ∧ (True → p4))) ∧ True))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233226556267755898590575201152 : ((p5 ∧ (p4 → False)) → (((((((False ∧ p1) → False) → p1) ∧ (True ∨ (p5 ∧ p4))) ∧ False) ∧ p4) ∨ (p2 ∨ ((p5 → True) ∨ (True ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89184118922269782555077701625 : ((((False → p2) → p3) ∧ (((((p3 → True) ∧ p2) ∧ ((((p1 ∨ True) ∨ ((p2 ∨ (p4 ∨ p4)) ∧ p5)) ∨ p3) ∨ p2)) ∨ False) ∧ p4)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h15 : (False → p2) := by
              -- Implications on the right can always be decomposed.
              intro h16
              -- False on the left can always be used.
              apply False.elim h16
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h17 := h2 h15
            -- One of the premise coincides with the conclusion.
            exact h17
          case inr h18 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h19 : (False → p2) := by
              -- Implications on the right can always be decomposed.
              intro h20
              -- False on the left can always be used.
              apply False.elim h20
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h21 := h2 h19
            -- One of the premise coincides with the conclusion.
            exact h21
        case inr h22 =>
          -- Conjunctions on the left can always be decomposed.
          let h23 := h22.left
          let h24 := h22.right
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h25 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h26 : (False → p2) := by
              -- Implications on the right can always be decomposed.
              intro h27
              -- False on the left can always be used.
              apply False.elim h27
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h28 := h2 h26
            -- One of the premise coincides with the conclusion.
            exact h28
          case inr h29 =>
            -- Disjunctions on the left can always be decomposed.
            cases h29
            case inl h30 =>
              -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
              have h31 : (False → p2) := by
                -- Implications on the right can always be decomposed.
                intro h32
                -- False on the left can always be used.
                apply False.elim h32
              -- We have shown the premise of h2, we can now drive its conclusion.
              let h33 := h2 h31
              -- One of the premise coincides with the conclusion.
              exact h33
            case inr h34 =>
              -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
              have h35 : (False → p2) := by
                -- Implications on the right can always be decomposed.
                intro h36
                -- False on the left can always be used.
                apply False.elim h36
              -- We have shown the premise of h2, we can now drive its conclusion.
              let h37 := h2 h35
              -- One of the premise coincides with the conclusion.
              exact h37
      case inr h38 =>
        -- One of the premise coincides with the conclusion.
        exact h38
    case inr h39 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h40 : (False → p2) := by
        -- Implications on the right can always be decomposed.
        intro h41
        -- False on the left can always be used.
        apply False.elim h41
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h42 := h2 h40
      -- One of the premise coincides with the conclusion.
      exact h42
  case inr h43 =>
    -- False on the left can always be used.
    apply False.elim h43



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171453677253521944882652556044 : (((p3 ∧ (p5 ∧ ((p5 ∧ p1) → (p2 → (p3 ∨ (p2 ∧ (True ∧ p1))))))) ∧ p1) ∨ (((p1 ∨ ((p3 → True) ∨ (p2 ∧ p2))) ∨ p5) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_38202571874563624921239421974 : (((((p1 ∧ ((((((True ∨ p1) ∨ p5) ∧ True) ∧ (True ∨ p1)) ∧ (p5 ∧ p5)) → (p2 ∧ False))) → p4) → ((p3 ∨ True) ∧ p2)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717846981305361810910298707374 : (((((p2 ∧ (p5 → p3)) ∧ p4) ∨ ((((((((p4 → p4) → p5) ∧ p5) ∧ False) ∨ (p4 ∧ p2)) ∨ p4) ∨ (p2 → (p4 → p4))) ∨ p4)) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78604983793870042990405208066 : ((((p4 ∧ (((True ∨ True) ∧ (p3 → p3)) ∧ (p3 ∧ ((((p5 → True) → p4) ∨ (p2 → p1)) ∧ p3)))) ∨ (p4 ∧ p3)) ∧ (p4 → p5)) → p5) := by
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
      let h12 := h8.left
      let h13 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h17 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h18 := h3 h17
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h19 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h20 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h21 := h3 h20
        -- One of the premise coincides with the conclusion.
        exact h21
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h8.left
      let h24 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h27 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h28 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h29 := h3 h28
        -- One of the premise coincides with the conclusion.
        exact h29
      case inr h30 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h31 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h32 := h3 h31
        -- One of the premise coincides with the conclusion.
        exact h32
  case inr h33 =>
    -- Conjunctions on the left can always be decomposed.
    let h34 := h33.left
    let h35 := h33.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h36 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h34
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h37 := h3 h36
    -- One of the premise coincides with the conclusion.
    exact h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152220089179139561703720083624 : ((((p2 ∨ p5) ∨ (p5 ∨ (p4 ∧ p4))) ∧ ((((p3 → p4) ∧ False) → (p1 → False)) ∨ ((False ∨ False) → p3))) → (p4 ∨ ((False ∨ False) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- False on the left can always be used.
          apply False.elim h8
        case inr h9 =>
          -- False on the left can always be used.
          apply False.elim h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- False on the left can always be used.
          apply False.elim h12
        case inr h13 =>
          -- False on the left can always be used.
          apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- False on the left can always be used.
          apply False.elim h18
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- False on the left can always be used.
          apply False.elim h21
        case inr h22 =>
          -- False on the left can always be used.
          apply False.elim h22
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h26
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- False on the left can always be used.
          apply False.elim h27
        case inr h28 =>
          -- False on the left can always be used.
          apply False.elim h28
      case inr h29 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h30
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- False on the left can always be used.
          apply False.elim h31
        case inr h32 =>
          -- False on the left can always be used.
          apply False.elim h32
    case inr h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h33.left
      let h35 := h33.right
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h36 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h35
      case inr h37 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165975037544890209932645319621 : (((p4 → p2) ∧ ((p3 ∧ ((False ∨ ((True ∧ p2) ∨ ((True ∨ p4) ∧ True))) ∧ p3)) ∧ True)) ∨ (p1 ∨ (p2 → (p5 ∨ (True ∨ (p5 → True)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185062522060339457260685288254 : (((p2 ∧ p1) ∨ ((((False ∨ p3) → p2) → p4) ∨ (p4 ∧ p3))) ∨ ((p2 → True) ∨ ((True ∧ p4) ∨ ((((p4 ∧ p4) → p2) → p3) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337663638201083333473053010159 : (p1 → (((p3 ∨ ((p5 → False) → (False ∨ (p4 ∨ p2)))) ∧ (p5 ∨ ((True ∧ p5) ∧ (p5 ∨ p3)))) ∨ (((False → p4) ∨ (p5 → True)) ∨ False))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244636398784135090579081005694 : ((False ∧ p5) ∨ ((False ∧ (((((p4 ∧ (False ∧ False)) → p5) ∧ True) → p3) ∨ p2)) ∨ (p1 ∨ (p4 → (False ∨ ((False → (p5 ∧ p2)) ∧ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64797527885091704668645088308 : ((p2 ∨ (((p1 → p5) ∨ ((True ∨ ((False ∨ True) → ((((p1 ∧ p2) ∨ True) ∧ ((False ∧ p5) ∧ p2)) ∨ (p3 ∨ p3)))) → p1)) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112877492910992962729133954887 : ((((p1 → (p5 ∨ p2)) → ((p4 ∧ ((((p1 ∨ False) ∧ p1) ∨ p1) → (p5 → p5))) → (p5 → ((p3 ∧ p2) → p3)))) → p2) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111835870435555560862421891172 : (((((((p4 ∨ p5) ∧ (((p3 ∨ p5) ∨ p5) → True)) ∨ (False ∨ (p4 ∧ p2))) ∨ (True ∧ True)) ∨ (p3 → (p4 ∧ p1))) ∨ p4) ∨ (p2 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87081744213787783652079389024 : ((((p2 → ((p3 ∧ False) → p5)) → (p4 → p4)) → ((((p3 ∨ (p4 → ((p3 ∨ (p5 ∧ (p5 ∨ p5))) ∧ p1))) → p1) → p4) ∧ False)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 → ((p3 ∧ False) → p5)) → (p4 → p4)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64512827453696933219884456331 : ((p1 ∨ ((((((p4 → (p5 → (p3 ∨ p2))) ∧ p4) → p2) ∧ False) ∨ True) ∨ (((p5 ∧ (True ∨ (p2 ∧ (p5 ∧ p1)))) ∨ p3) → True))) ∨ p3) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56431404539885370645318219901 : ((((False → p2) ∧ (True → p5)) → ((((p3 → p2) → (p4 ∨ (p1 → (p1 → p4)))) ∨ p1) ∨ ((True ∨ (p5 ∨ (p3 → p2))) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728930351767489205261294075366 : (((((False ∨ True) ∧ True) → (((((p2 → p2) → ((True → p3) ∧ (p4 → (p1 ∨ (p5 ∧ ((p3 → p5) ∧ p4)))))) ∨ True) ∧ False) ∨ True)) ∨ p3) ∧ True) := by
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
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207906542343680305296367015855 : (((p2 ∧ (p4 ∨ p5)) ∧ (p2 ∧ p2)) → ((False → (False → False)) → (False ∨ ((((p4 ∨ True) → (((p5 ∨ p3) → p5) ∨ p3)) ∨ p5) ∨ True)))) := by
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
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h4.left
    let h9 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h4.left
    let h12 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48026657519460864772867501008 : ((((((False → p3) → (p2 → p5)) ∨ (((False ∧ False) ∨ p2) → p4)) → (p3 ∨ (p5 ∧ (((p2 ∧ p2) → p2) ∧ True)))) → (p5 → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349582707252351487892809556142 : (p4 → (((p2 ∨ ((((p4 ∧ True) → (p2 ∨ p3)) ∨ ((p2 → ((p3 ∧ p4) ∧ p2)) → p2)) → (p5 → ((p1 ∨ p2) ∨ p4)))) ∨ p3) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40050596916940153333027131409 : (((((((((p2 ∨ (p5 ∨ False)) ∨ ((p3 ∨ (p3 ∧ (p5 ∧ p2))) ∧ p2)) ∨ (False → p1)) ∨ (False ∨ True)) ∨ False) ∨ False) ∧ True) ∨ p2) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340786165074325852272851305163 : (p2 → (((((((p3 → (p4 → (False → (p3 ∧ p4)))) ∨ p5) ∧ p3) ∧ p4) → ((p1 ∧ ((p1 ∧ p1) ∧ True)) ∨ (True → p4))) → p5) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111024169961446266625058380435 : ((((((p1 ∧ (p4 ∨ (p2 ∧ p1))) ∨ p3) → ((True → (p3 ∨ p1)) ∧ ((p2 → p2) → True))) → (p3 ∨ (p2 ∨ p4))) ∧ p4) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330940085327296322651032266419 : (True → (p4 → (True ∧ ((((p5 → p5) ∧ (p5 → True)) ∨ (((p3 ∧ p5) → (True ∧ False)) → (p3 → p3))) → (((p2 ∨ p4) → False) → p5))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h8 : (p2 ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h11 : (p2 ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h12 := h4 h11
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133567522548388475780586288592 : (((((((p5 ∨ ((p4 → (p4 → p4)) → p1)) ∧ (((False → False) ∨ False) ∨ p2)) → False) ∨ (False → p4)) ∨ p3) ∧ True) ∨ (p1 ∧ (False → p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_54047505930079174394181814761 : ((((True → ((p2 ∧ p5) ∧ p4)) ∧ ((p4 ∨ p3) ∧ p4)) → (((((p5 ∨ True) ∧ p3) → False) ∨ (p4 ∨ (True ∨ p1))) ∧ (False → p5))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h4
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h8
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42252810643174943623204456688 : (((p1 ∧ ((p4 ∨ ((p1 ∧ ((p3 → (p2 → False)) → p3)) ∧ (((((p2 → p3) ∨ p3) ∧ p5) ∨ p4) → (p4 ∧ True)))) ∧ True)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787035768952374711565568317559 : (((p4 ∨ ((p1 ∧ p1) ∨ ((((p3 ∧ (((False → ((p1 ∨ p4) ∨ p3)) ∧ (p5 → (True ∧ (p4 → p2)))) ∨ p4)) ∨ p4) ∨ True) ∨ True))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_214609200531969670967966261029 : (((p5 ∨ p5) ∧ (p1 ∧ True)) ∨ (((((((p4 → True) ∧ p3) ∨ True) ∨ (p1 → True)) ∧ (p1 → (p2 ∧ (p1 ∨ p3)))) → p5) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689824810285284951667813794336 : (((((False → p2) ∧ (((True ∨ (p5 ∨ p4)) ∧ p3) ∧ ((True ∨ (p1 ∧ p5)) ∧ p5))) ∨ ((p5 ∨ ((p3 → p4) ∧ p5)) ∨ (p2 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346355537425317135880471658271 : (p3 → (((p5 → (True ∨ False)) → ((True ∧ (p2 ∨ (p2 ∨ ((p5 ∨ (p2 ∧ (p5 ∨ True))) ∧ p2)))) ∧ ((p3 → p1) → True))) ∨ (p5 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62369202011453293590297390202 : ((p3 ∧ (((((p5 → p1) ∨ p5) ∨ True) → (False ∨ ((False → False) ∧ (p1 ∧ (p2 ∨ p5))))) ∨ ((p2 ∧ p2) ∧ (False ∨ (p5 ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157222065744175542551079260937 : (((((p4 ∨ (p4 ∨ (p2 → ((p3 ∨ (p1 ∧ p5)) → False)))) ∧ p3) → (p2 → (p4 ∧ p4))) → p3) ∨ ((True ∨ ((p2 ∧ p4) ∧ True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172985368731660593592113744142 : ((p5 ∧ (((p1 ∨ ((((True → p3) ∧ p2) ∨ (p3 ∧ p1)) ∧ p4)) → p1) ∧ False)) ∨ (False ∨ ((p2 ∧ ((p4 ∧ False) ∧ p2)) → (p5 → True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135475496589286482974033726507 : (((((((p2 ∧ p3) ∨ (p4 ∨ p4)) → p1) ∨ p4) ∧ ((((False ∨ p3) ∧ p1) ∨ True) ∨ p2)) → (p4 → (False ∨ p4))) ∨ ((p4 → p1) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h10 =>
          -- False on the left can always be used.
          apply False.elim h10
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h19 =>
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14



