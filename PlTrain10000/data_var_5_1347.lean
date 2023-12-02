variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213132794476171445699237013134 : ((((p2 → p4) ∧ False) ∧ True) ∨ (((p2 ∧ ((p5 → (False ∨ p1)) ∨ (p3 → ((True → True) → p5)))) → (p5 ∧ (p1 ∧ p4))) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147649083698634812567455874979 : (((((p4 ∧ (True ∧ (p4 → (True ∧ ((p5 → (p5 ∨ p1)) ∧ (p1 ∧ p3)))))) ∧ p4) ∧ (p5 ∨ p5)) → p1) ∨ (False ∨ ((True ∧ p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65917052620528446652477502970 : ((p4 ∨ (p4 ∧ ((((p2 ∨ (((p4 → p3) ∧ p5) → (((p4 ∧ (((p5 ∧ p2) → p4) ∨ p1)) → p4) ∧ True))) ∨ p5) → p4) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64846778475612473795025367279 : ((p2 ∨ ((p1 → (((p4 → (p1 ∨ ((p5 ∧ p2) ∨ True))) → (p2 → False)) ∧ ((False → ((p1 ∧ (p2 ∨ True)) → p5)) ∨ True))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316703491367512920962926183763 : (p3 ∨ (p5 ∨ ((p4 ∧ p3) ∨ (((p5 → False) ∨ (((False ∧ False) → True) ∧ ((p3 ∧ p1) ∨ (p3 → (p3 ∨ p2))))) ∨ (p4 ∨ (True ∧ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192551727450426415787495160403 : (((p5 ∧ (p3 → (p2 → ((p3 ∧ True) → p1)))) ∨ False) → ((p3 ∧ p1) ∨ ((p3 ∨ (p3 → p2)) ∨ (False → (p3 ∨ ((p5 ∨ False) ∧ False)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205237002339221926013089111755 : ((((False ∧ p3) ∨ p1) ∨ (p2 ∨ p3)) ∨ ((False ∧ (False ∨ ((p2 ∧ p5) → (p2 ∨ p5)))) → ((((p3 → (True → False)) ∧ p5) → True) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134045792328304594294722021294 : (((((p2 ∨ False) ∨ (((((p2 ∧ p2) → True) → (p5 ∧ True)) ∧ ((p1 ∨ True) → p3)) ∨ (p2 → True))) ∨ p2) ∨ p2) ∨ ((p1 ∨ False) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_135279810826378012657403706121 : (((True → ((True ∧ p2) ∨ (((False → p4) ∨ ((False ∧ (p5 → p3)) ∧ p5)) → (p1 ∧ (p2 ∧ p3))))) → (p3 ∧ False)) ∨ ((True ∨ p5) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225215656231030222145257257644 : (((p5 ∧ False) ∧ p2) ∨ (p5 → ((((p5 ∨ (p4 ∨ ((p1 ∨ (p1 ∧ (True ∨ ((p4 ∨ p2) → p3)))) → p5))) ∧ p3) ∧ p1) → (p4 ∨ p3)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616698343991490302000068664593 : (((((((((p3 → True) ∧ False) → p1) ∧ (p5 ∨ p1)) ∨ p3) ∨ (True ∧ (((True → True) → (((p3 ∧ p4) ∧ p4) ∨ p1)) ∨ False))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90930191008236881393396180341 : (((True → p2) ∧ (((((((p2 ∧ True) ∧ p4) ∨ ((True ∧ False) ∧ (p5 ∨ (p3 ∧ p1)))) ∨ p5) ∧ False) → ((True ∧ p2) ∨ p4)) ∨ False)) → p2) := by
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
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612531353764553109204194586906 : ((((((p2 ∧ (p4 ∨ (p1 ∨ ((p1 → (((p2 ∨ (p1 ∧ p3)) ∧ ((p1 ∧ p2) → p3)) ∨ p4)) ∧ p4)))) ∨ False) ∨ (True → True)) ∨ p1) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_96484260749947963794091517270 : ((False ∨ ((((p4 ∨ p2) ∨ p2) ∧ p1) ∧ ((((p4 → p1) ∨ (p5 ∨ (((p1 → p4) → p3) → False))) → p5) ∧ ((True → p2) ∨ p1)))) → p5) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h5.left
        let h11 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
          have h13 : ((p4 → p1) ∨ (p5 ∨ (((p1 → p4) → p3) → False))) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h14
            -- One of the premise coincides with the conclusion.
            exact h7
          -- We have shown the premise of h10, we can now drive its conclusion.
          let h15 := h10 h13
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h16 =>
          -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
          have h17 : ((p4 → p1) ∨ (p5 ∨ (((p1 → p4) → p3) → False))) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h18
            -- One of the premise coincides with the conclusion.
            exact h16
          -- We have shown the premise of h10, we can now drive its conclusion.
          let h19 := h10 h17
          -- One of the premise coincides with the conclusion.
          exact h19
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h5.left
        let h22 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
          have h24 : ((p4 → p1) ∨ (p5 ∨ (((p1 → p4) → p3) → False))) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h25
            -- One of the premise coincides with the conclusion.
            exact h7
          -- We have shown the premise of h21, we can now drive its conclusion.
          let h26 := h21 h24
          -- One of the premise coincides with the conclusion.
          exact h26
        case inr h27 =>
          -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
          have h28 : ((p4 → p1) ∨ (p5 ∨ (((p1 → p4) → p3) → False))) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h29
            -- One of the premise coincides with the conclusion.
            exact h27
          -- We have shown the premise of h21, we can now drive its conclusion.
          let h30 := h21 h28
          -- One of the premise coincides with the conclusion.
          exact h30
    case inr h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h5.left
      let h33 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h34 =>
        -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
        have h35 : ((p4 → p1) ∨ (p5 ∨ (((p1 → p4) → p3) → False))) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h36
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h32, we can now drive its conclusion.
        let h37 := h32 h35
        -- One of the premise coincides with the conclusion.
        exact h37
      case inr h38 =>
        -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
        have h39 : ((p4 → p1) ∨ (p5 ∨ (((p1 → p4) → p3) → False))) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h40
          -- One of the premise coincides with the conclusion.
          exact h38
        -- We have shown the premise of h32, we can now drive its conclusion.
        let h41 := h32 h39
        -- One of the premise coincides with the conclusion.
        exact h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137811493108542475764240283264 : ((p3 ∨ ((((((p3 → p5) ∧ p1) ∧ True) ∨ p1) ∧ (((((p5 ∨ p5) → p4) → p2) ∨ True) → (p5 ∨ p2))) ∧ True)) ∨ (False → (p2 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705078448847147852663630799796 : ((((p4 → ((p3 ∨ p5) ∧ (p4 ∨ ((True → p3) ∨ p4)))) → ((((p4 ∨ p3) → p3) ∨ (p1 → ((p4 ∨ p3) → False))) ∧ (True ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163989739105345061897367182545 : ((True ∨ ((((((False → (p4 ∨ p3)) ∧ (p4 ∧ p4)) ∧ False) ∧ (p2 ∧ False)) ∨ p3) ∨ p5)) ∧ (p2 ∨ ((p3 ∧ ((p2 ∨ p4) ∧ p5)) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685560069029401405458913489230 : (((((p4 → (False → (False ∧ (((p2 ∧ False) ∨ (p2 ∧ (p4 ∨ (p4 ∧ False)))) ∨ p1)))) ∧ p5) → (False ∧ (((p1 ∨ True) → p4) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_940311608583108644620924922519 : ((((((True ∨ (True ∨ p4)) ∧ True) ∨ p4) → (True → (True → ((p5 ∧ ((p3 ∨ p1) ∧ ((p2 → p2) ∨ (p1 → (p2 ∨ p5))))) ∧ p2)))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True ∨ (True ∨ p4)) ∧ True) ∨ p4) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265589980786459813113974611084 : (True ∧ (p1 ∨ ((p3 ∧ (((p4 → ((p1 ∨ (p4 → p1)) ∨ (p4 ∨ False))) ∨ ((p1 ∧ p4) → p4)) → (p2 → p4))) → ((True → False) → p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_821797531864999437305451973121 : (((((((p5 → False) ∧ (p5 → (False → (p2 ∧ (p4 ∧ False))))) ∧ p3) ∧ (p4 → ((p3 ∧ False) ∧ (((p3 ∧ p5) ∨ p2) ∨ False)))) ∧ p4) → p5) ∧ True) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h10 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h11 := h5 h10
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- False on the left can always be used.
  apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234570390517422316686880819839 : ((p3 → (p5 ∧ False)) → ((p5 → ((p1 ∨ ((p3 ∨ p3) ∨ p5)) ∧ ((p5 → False) → ((((p1 ∧ p2) ∧ p5) ∧ p3) ∧ p1)))) ∨ (p3 ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- One of the premise coincides with the conclusion.
  exact h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h8 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h10 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h11 := h3 h10
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354789252129416828348062931240 : (p5 → (((((False ∨ (p3 ∧ p2)) ∧ False) ∨ p3) ∧ ((((True ∨ False) ∧ (p5 ∧ p2)) → True) ∨ ((False ∨ ((True ∧ p5) → p3)) ∨ p2))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308130801340830910073555800919 : (p2 ∨ (((((True ∨ (p4 ∨ (p2 → p4))) ∨ False) → p1) → (((p4 ∧ (p3 → (p4 ∨ p5))) ∨ False) ∨ ((p2 → (p3 ∧ p3)) → p1))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((True ∨ (p4 ∨ (p2 → p4))) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233765321143271881474147863314 : ((p3 ∨ (p2 ∨ True)) → ((((p2 ∧ p4) ∧ ((((p3 → p4) ∨ p4) → (p2 ∨ (True → p4))) ∧ p3)) ∨ (True ∨ ((p3 ∧ p1) ∧ p2))) ∨ p3)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256382598427414986128792433925 : ((False ∨ p2) → (True → ((((((True ∨ p4) ∧ True) → (True → ((p1 ∨ False) ∧ (((p3 ∧ (True ∨ p5)) ∨ p5) ∨ p2)))) ∧ p4) ∧ True) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112948030357045230023388270307 : (((True ∧ ((((p4 ∨ (p4 ∨ (False → (p5 ∧ p3)))) ∨ (p4 ∨ p1)) ∧ (p5 → (p1 → (p1 ∧ p4)))) → (p1 ∨ p4))) → p4) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136826418435745126735672484879 : (((False ∧ False) ∨ ((p3 ∧ ((((p3 → (((p1 ∨ p5) ∧ p4) ∨ (p4 → (p5 ∧ p3)))) ∧ p2) ∨ p2) → p4)) ∧ True)) ∨ ((p3 ∨ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805559940644873788429074720659 : (((p3 → (p5 ∨ (((((((p1 ∨ (p5 ∧ (p2 → p5))) ∧ ((False ∨ p5) → p2)) ∧ True) → p4) → (p4 ∧ p4)) ∧ p4) ∨ (p3 ∨ p3)))) ∨ p3) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765992230182552795501420711013 : (((p4 ∧ (((p1 ∨ True) ∧ p5) ∧ (p3 ∧ (((p1 ∨ (p2 ∧ p2)) → ((True → ((p4 ∧ p3) → p4)) ∨ p5)) → (p3 ∨ (p3 → p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139591252578465300225323663576 : ((((((((p5 ∧ (p3 ∨ p3)) ∨ p3) ∧ p5) → ((p2 → False) ∧ True)) ∨ p4) ∨ (p3 → ((p3 → p2) → p5))) → False) → ((p2 ∧ p5) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : ((((((p5 ∧ (p3 ∨ p3)) ∨ p3) ∧ p5) → ((p2 → False) ∧ True)) ∨ p4) ∨ (p3 → ((p3 → p2) → p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h5
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135480055877012418432741744375 : ((((((True → False) ∨ p3) ∧ (p2 → p2)) → (((p5 ∨ (p5 → p3)) ∧ p3) → (p5 → False))) → ((p1 ∧ p1) ∧ False)) ∨ ((True ∨ p5) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113691673269283903534946355930 : ((((((p4 ∨ True) ∨ (p1 ∧ (((True ∨ p4) ∨ p5) ∨ (p1 → p4)))) ∨ (p1 ∨ ((False ∨ p2) ∧ True))) → p3) → (p5 ∧ False)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110807642923189965159176434770 : (((((((p2 → False) ∧ (p2 → p3)) ∧ (((True ∨ p4) → p2) → p3)) ∧ (True → (p2 → ((p2 ∨ p3) → p3)))) ∨ p5) ∧ p1) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4611265608267871142406136129 : (p4 → (p4 ∧ (((((p3 ∧ (p3 → True)) ∧ True) ∨ p5) ∧ ((p2 ∨ p4) ∧ (p4 → (((p5 ∧ p1) ∨ p3) ∨ p1)))) ∨ (p4 → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198700779857025304501405972144 : ((p5 ∨ ((((p1 ∨ False) ∨ p4) ∧ p2) ∧ p4)) ∨ (False → (((p1 ∨ p1) ∨ p3) ∧ (p5 → ((p3 ∨ p2) ∨ ((p4 ∧ p1) ∨ (p2 ∨ p4))))))) := by
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
theorem thm_5_vars_886248595110236690389416331 : ((p1 → ((True → (True ∨ ((p5 ∧ (p5 ∨ (p1 ∨ ((p5 → p4) ∨ False)))) → p4))) → (p3 ∧ (p4 → ((p3 ∨ p2) ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37568028570637519331775779108 : ((((p5 ∨ ((((p1 ∨ (False ∨ p3)) ∧ ((False → ((((True ∧ (p3 ∧ p3)) → p2) ∧ False) ∧ p5)) ∨ p5)) → p1) ∨ p1)) ∨ p3) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112403588495235024490091274077 : (((((p4 ∨ p5) → ((True ∨ (((False ∨ ((True → (p3 ∧ (p5 ∧ p4))) → (p1 ∨ p2))) → p3) ∧ p5)) → p1)) ∧ True) → p2) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350012784845618987071931063203 : (p4 → (((p4 → (True → ((((((p3 ∨ ((p4 ∧ p2) → p5)) ∨ p3) → (((False ∧ p5) → True) ∧ p2)) ∧ p1) ∨ True) → p3))) ∨ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175068247380004250212713132541 : ((p3 ∧ ((((True ∧ (p2 ∨ p4)) ∨ p2) ∨ (p5 ∨ ((False → p4) ∨ p4))) ∧ p3)) → (p1 ∨ ((((p1 → p3) ∨ False) → (False ∨ p3)) ∨ p5))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h13 =>
          -- False on the left can always be used.
          apply False.elim h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h15
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h17 =>
          -- False on the left can always be used.
          apply False.elim h17
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h19
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h21 =>
        -- False on the left can always be used.
        apply False.elim h21
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h23
    case inr h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h26
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h28 =>
          -- False on the left can always be used.
          apply False.elim h28
      case inr h29 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h30
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h32 =>
          -- False on the left can always be used.
          apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172210056331265339063030144504 : ((((p3 ∨ (p3 ∧ p2)) ∨ (((p5 → p5) ∨ p4) → False)) → (p4 ∧ (False ∨ p2))) ∨ (False ∨ ((p4 ∨ p4) ∨ ((p3 → (p4 → p2)) → True)))) := by
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
theorem thm_5_vars_184695206688425760337170698895 : (((((False → True) ∧ (p5 → p3)) ∨ p2) → (p3 ∧ (False ∧ p2))) ∨ (((True ∧ (((p3 ∨ True) ∧ p1) ∧ False)) ∧ True) ∨ ((p3 ∨ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256810445197262843607640962185 : ((p1 ∨ p2) → (p2 → ((p2 → (((True ∨ p1) ∨ p3) ∧ (p5 ∨ (p4 ∧ p1)))) ∨ (((False ∧ (p2 ∧ p2)) ∨ ((True ∨ p5) ∧ p5)) ∨ p2)))) := by
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
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110748646348565907174246308982 : (((((p1 → False) ∨ (False ∧ (((((p3 ∨ p1) → p1) ∨ (p1 ∨ ((p4 ∧ (p2 ∨ p3)) ∧ False))) ∧ p1) ∧ p3))) ∧ p5) ∧ p4) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717323230930725016181771991104 : ((((p5 ∨ ((p4 → p1) ∧ True)) ∧ ((p1 ∧ (p2 ∧ (((True ∨ p4) ∨ p2) → False))) → (p1 → (((False ∧ (False ∧ p3)) ∨ True) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152088933328080593777443260988 : ((((((True ∧ p1) ∧ p1) ∨ (p4 ∨ p3)) ∨ (p2 ∨ False)) → (((p4 ∧ True) ∧ (True → p2)) ∧ (p5 ∧ p1))) → (p3 → (p4 → (p2 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : ((((True ∧ p1) ∧ p1) ∨ (p4 ∨ p3)) ∨ (p2 ∨ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633413681903683011440431122815 : ((((((p4 ∧ (((p3 ∨ p2) → False) ∧ ((((False → p5) ∨ (p4 ∧ ((p2 → p3) → p4))) → p2) → p1))) → p1) ∨ (p2 → p4)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353443490731052564392893225435 : (p4 → (p1 ∨ ((True ∨ False) ∧ ((((p4 ∧ ((((p5 ∨ ((False ∧ p1) → (True ∧ p1))) ∧ (p2 → p3)) ∧ p5) ∨ False)) ∨ p5) ∧ False) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327155071866092972173080806320 : (True → ((p4 ∧ ((((((False → p1) ∧ (((p1 ∨ p1) → (p3 ∧ (True ∨ p2))) ∨ p5)) ∨ ((p1 → p5) ∧ p2)) → p1) ∧ p2) ∨ p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50196380850031284024518452308 : ((((p4 ∨ (p5 ∨ (p5 ∧ (((p1 ∨ p5) → True) ∧ (((p3 ∧ True) → (p1 ∨ False)) → False))))) ∧ p3) ∨ ((p2 → False) ∨ (p4 → True))) ∨ False) := by
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
theorem thm_5_vars_123202518125142307441367518486 : (((((((p4 ∧ (p5 ∨ (True ∨ p1))) → (False ∨ p2)) ∨ p2) → ((p3 ∧ False) ∧ p2)) ∨ False) ∧ (p1 ∨ ((p2 → p1) ∧ p4))) → (p2 → p3)) := by
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
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h7 : (((p4 ∧ (p5 ∨ (True ∨ p1))) → (False ∨ p2)) ∨ p2) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h8 := h5 h7
      -- We need to get the left conjuct of h8 based on <expert-advice>.
      let h9 := h8.left
      -- We need to get the left conjuct of h9 based on <expert-advice>.
      let h10 := h9.left
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h14 : (((p4 ∧ (p5 ∨ (True ∨ p1))) → (False ∨ p2)) ∨ p2) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h15 := h5 h14
      -- We need to get the left conjuct of h15 based on <expert-advice>.
      let h16 := h15.left
      -- We need to get the left conjuct of h16 based on <expert-advice>.
      let h17 := h16.left
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h18 =>
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205951961092484056291710938108 : ((False ∧ (p2 ∨ (p4 ∨ (p2 ∧ p4)))) ∨ ((False → (((p5 ∧ True) ∧ (True ∨ (((True ∧ p2) → p3) → p1))) ∧ (p1 → (False → p2)))) ∨ p3)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349030707282769449839078503382 : (p3 → (p5 ∨ ((((p2 → False) ∧ (p3 → (p4 → (p3 ∨ (p2 ∧ (p1 ∨ (((p4 ∨ p2) → (p5 ∧ (p4 ∧ False))) ∧ p3))))))) → p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263879307364570564427703002704 : (True ∧ ((((((False → ((p2 → (p1 ∧ p3)) ∨ p2)) → p1) ∨ p2) ∧ p4) ∧ p3) ∨ (p3 → ((p2 → p1) → (p4 ∨ ((p3 → True) ∨ True)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_248150620749591341233397685733 : ((p2 ∨ False) ∨ (((((p4 ∧ p5) → (p5 ∧ ((True ∨ p3) ∧ ((p2 ∨ p2) ∨ False)))) ∨ ((p1 ∨ p3) ∧ p5)) ∨ True) ∧ ((p3 ∧ p4) → True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684103257752861600196656451569 : ((((((p2 ∨ (p3 ∧ ((p2 ∨ ((p2 → p4) ∨ p3)) → False))) ∨ (p3 → True)) ∧ (p1 ∧ p2)) ∨ ((p5 → (True → True)) → (p3 → p3))) ∨ p2) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351633835653329330256814761194 : (p4 → (((((p5 ∨ (p3 ∨ ((p5 → p1) → p2))) → (p5 ∧ p4)) ∨ p5) → (p1 ∧ False)) ∨ (p4 → ((p5 → p1) → ((p4 ∨ True) ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640050076806833340406681096027 : (((((p4 → (False ∧ False)) ∨ (((((p4 → True) ∨ p5) ∨ (((True → ((False ∨ False) → p2)) ∧ (p1 ∧ p5)) ∧ p5)) ∨ True) ∧ p1)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307164491361353129308785267824 : (p1 ∨ (False ∨ (p1 ∨ (p4 → ((((((p3 ∨ (p2 ∧ ((p5 → (p2 ∨ p1)) ∨ p4))) → p4) ∨ p2) → p5) ∧ p1) → ((False ∧ False) ∨ p4)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67599246951385980209060553347 : ((p1 → (False ∧ (p3 ∨ (((p4 ∨ ((p1 ∧ (True → (p5 ∨ ((p1 ∧ False) → ((p4 → (p1 → p2)) ∧ p5))))) ∧ p4)) ∧ p5) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48019329006491121682121468344 : (((((p4 → (False ∨ (True → (p5 → (p2 → p2))))) → (p1 ∧ p1)) ∨ (((True → p1) ∧ ((True ∧ p3) ∧ p4)) ∨ True)) → (p4 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327032797440489958205455820991 : (True → (((((p1 → False) → ((p1 ∨ (False ∧ p3)) → False)) → p1) ∧ (p2 ∨ (((True ∨ p1) ∨ p5) → ((p4 ∨ (p5 → True)) → p2)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303923482724236229889871054504 : (p1 ∨ (((((False → ((p2 ∧ False) → p4)) ∨ (p3 ∨ p5)) → False) → ((False ∧ ((((True ∧ p4) ∨ p1) ∨ (p2 ∨ True)) ∧ p3)) ∨ False)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False → ((p2 ∧ False) → p4)) ∨ (p3 ∨ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94800263912823824472509081450 : ((p3 ∧ ((True ∧ (p3 → False)) ∧ ((((p5 ∨ p3) → p5) → (p2 ∨ (False → (p4 ∨ ((p4 ∧ p2) ∧ p4))))) ∨ ((True ∧ False) → p3)))) → p4) := by
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
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h12 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h13 := h7 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150040591663102364763789693998 : ((p5 ∨ (p5 ∨ ((((p3 ∨ (p4 ∧ (False ∧ (False ∧ (p4 → False))))) ∧ False) → (p2 ∧ (False ∨ p4))) → p4))) ∨ (False ∨ (True ∨ (True → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66664101102941997969980451142 : ((True → ((((p1 ∨ p3) ∨ p2) ∨ (p2 ∧ p4)) ∧ ((p5 → p5) ∧ ((((p2 → p2) ∧ ((p1 ∨ False) → (p3 ∧ p4))) ∨ p3) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40419201908730996671506617833 : ((((((p1 → p5) ∧ (((p3 → (p4 ∧ p4)) ∧ (True → p4)) ∨ (p1 ∨ False))) ∧ ((p1 ∧ (p1 → (False ∨ p2))) ∧ False)) ∨ True) ∨ p3) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47142607973334080770404864260 : ((((p2 → ((False → p3) ∧ ((p5 → ((p3 ∨ False) ∧ p4)) ∨ (False ∧ (p1 ∨ p3))))) ∧ (((p1 → p5) → p4) ∧ True)) ∨ (p4 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51262940507618855176389475891 : ((((True ∧ True) → (((p4 → (True → p3)) ∧ True) → ((p1 → p2) → ((False → True) → p1)))) ∨ (((False ∨ p1) ∨ (p4 ∧ p1)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116825812499839036328479329498 : (((p5 ∨ False) ∨ (((True ∨ ((p1 ∨ p2) → (p4 ∨ (True ∧ ((p4 ∨ ((p3 ∧ p3) ∨ p1)) ∧ p1))))) → p4) → (p2 ∨ p4))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314162957798114843588758658377 : (p3 ∨ (((((p4 ∨ (p2 → (p3 → ((p3 ∧ ((False ∧ True) ∨ (p5 ∨ p4))) ∧ p1)))) → p2) ∨ (True ∨ p4)) ∨ p2) ∧ (p2 ∨ (False → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134516694810893207000775662719 : ((((p2 ∨ (((((((True ∨ p4) ∨ True) ∧ p5) ∨ p3) → False) ∨ p3) ∧ (True ∨ (True ∧ (p5 → p3))))) ∨ p1) → p4) ∨ (p3 → (True ∧ True))) := by
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
theorem thm_5_vars_53520244344123852249002518736 : (((p1 → ((p2 → (p4 ∧ (p4 ∧ p4))) → (p3 → (p3 → p3)))) → ((((p5 ∧ p3) ∧ (p3 ∧ (p3 → (p2 ∧ True)))) → p2) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137438587021131277422619043474 : ((p4 ∧ ((p3 → ((((p2 → (p5 ∧ ((p4 → p2) ∧ (p2 ∧ p4)))) ∧ p2) ∧ p3) ∨ True)) → ((p1 → p2) → p4))) ∨ ((True ∨ False) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116433793788421707396647663210 : (((p1 → (p1 ∧ p3)) → ((False → p5) ∧ (p3 → (((p3 → (((p2 ∧ p4) ∧ False) ∨ p5)) ∨ (p3 ∨ False)) ∨ (p1 → True))))) ∨ (p1 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218881612003272485271825804190 : ((p2 ∧ (p2 → (p5 ∨ p3))) → (((((((True ∧ True) ∨ ((p2 ∨ False) ∨ p5)) → p5) ∨ ((False ∧ (p2 ∨ p2)) ∨ p4)) ∨ p1) → p5) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- False on the left can always be used.
          apply False.elim h12
        case inr h14 =>
          -- One of the premise coincides with the conclusion.
          exact h6
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261530656011870207842133489853 : ((p5 → p3) → ((p5 ∧ p4) ∨ (((((p2 ∧ False) ∨ True) ∨ p5) ∧ (((p3 → p2) ∧ (False → p5)) → (p1 ∨ (p3 → (p2 ∨ p2))))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746225859970326902795476167292 : ((((p1 ∨ p4) → ((p4 → ((True ∧ True) ∧ (((p2 ∨ p4) ∨ (True → True)) ∧ ((p2 → ((False → True) ∧ p5)) → p2)))) ∧ (p1 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148380536796002175221937792685 : ((((False ∧ ((True ∨ p2) → (p2 ∧ (p4 ∧ p4)))) ∧ (p1 ∨ (p1 ∨ p3))) ∨ ((True ∨ False) ∧ (p1 ∨ p2))) ∨ (p2 ∨ (p2 → (p4 ∨ True)))) := by
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
theorem thm_5_vars_197478943635864529336860075564 : ((((p3 → p2) ∨ (p4 → False)) ∧ (p1 → True)) ∨ ((p2 ∨ (((p2 → (False → p2)) ∨ ((False ∨ p4) ∨ p1)) → (p1 ∧ (False ∨ p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190175422262316945145204411559 : (((p4 ∧ ((True ∧ (p2 ∧ (p1 ∨ p1))) ∧ p5)) ∧ False) ∨ (True ∨ ((True ∨ (False → (True → ((p3 ∨ True) → p3)))) ∨ ((p5 → p1) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225726671105132636664933326460 : (((p4 → False) ∧ p2) ∨ (((p4 ∧ (((p3 ∧ p3) ∧ (((p3 → False) ∨ False) ∨ p3)) ∨ (True ∨ False))) ∨ ((p2 → p2) → (True ∧ True))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299467863829781732275211523808 : (False ∨ ((True → ((True → (((True ∨ p5) ∧ (False ∧ (((p1 → False) ∨ True) → p2))) ∧ (p2 → ((p5 ∧ (p1 ∧ p5)) ∨ p4)))) ∨ True)) ∨ p4)) := by
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
theorem thm_5_vars_147383925767816336891640015736 : (((((((p5 ∨ p2) ∨ (p4 ∧ (p4 → p4))) → p1) → p3) → (((p4 ∧ (True → False)) ∧ False) ∨ p4)) ∨ p4) ∨ ((p3 ∧ p4) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666418121020048439734104399 : (((((p3 ∨ (p3 ∧ ((p1 ∧ True) → ((p4 ∧ p3) ∧ p2)))) ∧ (p1 ∨ (p3 ∨ p3))) → True) → (((True ∨ p2) → False) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315482006026650071487730426568 : (p3 ∨ (((True → False) → p3) → (p2 → ((p1 → ((p5 ∨ p3) → p1)) ∧ ((((False ∧ True) ∧ ((p2 ∧ (p3 ∧ p3)) → p1)) ∨ p2) ∧ True))))) := by
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
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218908565868820869594102992402 : ((p3 ∧ ((p5 → p1) ∨ True)) → ((p1 ∨ p3) ∧ (True → (((p1 ∧ (p3 ∨ True)) ∧ ((False ∨ p3) ∧ ((p5 ∨ (True → p1)) → p3))) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h9.left
    let h14 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h1.left
      let h18 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h20 =>
        -- One of the premise coincides with the conclusion.
        exact h10
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h9.left
    let h23 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h24 =>
      -- False on the left can always be used.
      apply False.elim h24
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h1.left
      let h27 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h29 =>
        -- One of the premise coincides with the conclusion.
        exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133974879661766984018558552878 : ((((((p2 ∨ ((p3 ∨ (True ∨ (p5 ∧ p1))) ∧ p3)) ∨ (((p1 ∨ p4) ∨ p1) ∧ (p3 → p4))) ∧ p3) ∧ p3) ∨ True) ∨ (p3 ∧ (p2 ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227941605010089661130957777551 : ((p3 ∧ (p2 ∧ p1)) ∨ ((((((p5 → p2) → True) → (True ∨ (False ∧ (p1 → p2)))) ∨ (p5 → p1)) → p4) ∨ (p1 ∨ ((p3 ∧ False) → p3)))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47126902004540445136674439206 : (((((((p1 ∨ (p3 ∧ ((False ∧ p5) ∨ p5))) → p2) → p1) ∧ (p2 ∨ (p5 ∨ (p2 ∨ False)))) → ((p4 ∧ p3) ∨ p2)) ∨ (p3 ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241698747343929072621489015027 : ((p1 → True) ∧ (((p4 → (((((p1 ∧ p2) ∧ p1) ∧ (((p3 ∨ (((p2 ∨ False) ∨ False) ∧ True)) ∨ False) ∨ False)) ∧ p3) → p1)) → p2) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166478672567275604081920801852 : ((p3 ∨ (((((True → True) ∧ p2) → False) ∧ (p3 → (p1 → (p3 ∨ (p3 → p5))))) → p5)) ∨ ((p1 ∨ (p4 ∨ (False → (p1 → True)))) ∨ p4)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181331700399103001165295805531 : ((True ∨ (p1 ∧ ((False ∨ ((True ∧ p5) ∨ ((True ∨ p1) → False))) ∧ True))) → ((p5 ∨ (p2 ∨ False)) ∨ ((True ∧ (p1 → p5)) ∨ (p1 → p1)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h15 : (True ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h16 := h14 h15
        -- False on the left can always be used.
        apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779988691982221513528507415659 : (((p2 ∨ (((((p3 → (p5 ∨ p2)) ∨ p4) ∧ (True ∧ ((p4 → (((False ∨ (p4 → p1)) ∨ p4) → p1)) → p5))) ∧ p1) ∨ (p1 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256447181962040247541341345001 : ((False ∨ p3) → (p3 → (p4 ∨ (p1 ∨ (p2 → ((p1 → ((False ∨ False) ∨ ((p1 ∨ True) → (((False ∧ p5) ∨ p5) ∨ (p5 → p1))))) ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245878281710834035311908418143 : ((p3 ∧ p4) ∨ (p1 → ((((False → p3) ∨ (False → (False → ((p4 ∨ p1) → False)))) → p1) → (p2 ∨ ((p4 ∧ p5) ∨ (p2 → (p3 → p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156977704090785923492748304109 : ((((p3 → (True ∧ ((False ∨ p2) ∧ (True ∧ p5)))) ∧ (((False ∧ True) ∨ p3) ∧ (p3 → False))) ∨ p3) ∨ ((False ∨ (p5 ∧ (p1 ∧ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40729524152881835528486357984 : ((((((True ∨ p4) → (p3 ∧ False)) ∧ ((((((p1 → (p1 ∨ (p1 ∨ False))) → p5) → p3) ∧ p5) ∨ (p4 → True)) ∨ p4)) → p1) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231344145852489325692217576003 : (((True → p5) ∨ p2) → (((((p4 → p4) ∧ p5) ∧ (p2 → (p5 → (p3 ∨ ((p5 ∧ p3) ∧ ((True → p1) → (p3 → p2))))))) ∨ p5) ∨ True)) := by
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



