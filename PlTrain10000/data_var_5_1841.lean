variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62971547635606374949571263758 : ((p4 ∧ (p2 ∨ (((p2 → ((p3 ∧ p4) → p2)) ∨ (p4 ∨ (p3 → True))) ∧ (p4 ∧ (p5 ∨ (p3 ∨ ((p2 ∨ False) ∧ (p1 ∧ p5)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719569019755196743021134243103 : ((((p4 ∨ ((p4 → p2) ∧ p3)) ∨ ((p4 → ((p3 ∧ p3) ∨ (p1 ∨ (True ∧ ((p1 ∨ (p4 ∧ (False ∧ False))) → p1))))) ∨ (p3 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185200727610332130261016453106 : ((True ∧ (((p1 ∨ False) ∨ p1) ∧ (p5 ∨ (p5 ∧ (False ∨ p4))))) ∨ ((p2 → ((False ∧ p5) → (p5 → False))) ∧ ((p2 → True) ∧ (p2 ∨ True)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323781336895466987783995364386 : (p5 ∨ ((((p5 ∧ (((p5 → ((p5 → (p4 ∨ (p5 → False))) → p5)) ∨ True) ∧ True)) → False) ∨ p1) ∨ (((p5 → p5) ∨ p1) ∨ (False ∨ False)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258784109085904584850525726467 : ((True → False) → (((p3 ∧ (False → p2)) ∨ ((p1 → (p5 ∧ (p2 → p5))) ∨ ((p1 ∨ True) → p3))) → ((p2 ∨ ((p1 ∨ p2) ∨ False)) → p3))) := by
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
    cases h2
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h10 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h11 := h1 h10
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h13 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h14 := h1 h13
        -- False on the left can always be used.
        apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- One of the premise coincides with the conclusion.
          exact h19
        case inr h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h22 =>
            -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
            have h23 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h1, we can now drive its conclusion.
            let h24 := h1 h23
            -- False on the left can always be used.
            apply False.elim h24
          case inr h25 =>
            -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
            have h26 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h1, we can now drive its conclusion.
            let h27 := h1 h26
            -- False on the left can always be used.
            apply False.elim h27
      case inr h28 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h29 =>
          -- Conjunctions on the left can always be decomposed.
          let h30 := h29.left
          let h31 := h29.right
          -- One of the premise coincides with the conclusion.
          exact h30
        case inr h32 =>
          -- Disjunctions on the left can always be decomposed.
          cases h32
          case inl h33 =>
            -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
            have h34 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h1, we can now drive its conclusion.
            let h35 := h1 h34
            -- False on the left can always be used.
            apply False.elim h35
          case inr h36 =>
            -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
            have h37 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h1, we can now drive its conclusion.
            let h38 := h1 h37
            -- False on the left can always be used.
            apply False.elim h38
    case inr h39 =>
      -- False on the left can always be used.
      apply False.elim h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112687540302259746697888343424 : ((((((p3 → (p3 ∨ True)) ∨ (False ∧ (p3 → p1))) → ((p2 ∧ (False ∧ p2)) ∧ True)) ∧ (p5 → ((p2 ∧ p2) ∨ p5))) → p3) ∨ (p1 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p3 → (p3 ∨ True)) ∨ (False ∧ (p3 → p1))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208938378436955265018037307218 : ((p5 ∧ (p2 → ((True → p4) ∧ p5))) → ((False ∨ p2) → ((((p1 ∨ (False ∨ (p1 → False))) ∧ ((p4 ∨ p3) ∧ p2)) → (False ∧ p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141722223256642688749531544417 : (((p3 ∨ p5) ∧ ((p3 ∧ (((((p4 ∧ (p4 ∧ p4)) → p1) → (p5 ∧ p4)) ∧ False) → p4)) ∨ ((p5 → p5) ∨ True))) → ((p2 → p4) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
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
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355402588677642190106208350212 : (p5 → ((p5 → (((p5 ∧ (p1 ∨ p5)) ∧ (True → ((p2 ∨ ((((p5 → False) → p3) ∧ (p2 → False)) ∨ p1)) ∧ (p1 → False)))) ∧ p4)) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205359406206143394437707607589 : ((((True → p2) ∧ p3) → (False ∨ False)) ∨ (((False → (((p1 ∨ p2) ∨ p5) → ((p3 ∧ (p5 ∧ p4)) ∧ True))) → False) ∨ ((p1 → p1) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66184408651820089709814812384 : ((p5 ∨ ((p1 ∨ ((p1 → (((True ∧ (True ∨ p4)) ∨ p2) ∧ (False ∧ (p1 ∧ (p1 ∧ True))))) → p2)) ∨ (p3 → (True ∧ (p5 ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60593850704920797679945401452 : ((True ∧ ((p4 ∨ (p2 → ((p2 → (((p2 ∨ p2) ∨ ((p1 → p2) ∨ p3)) ∧ p1)) ∧ ((p3 → True) ∨ (p2 ∧ (True ∨ False)))))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49318435811880271901762565184 : (((p3 ∨ (((((p1 ∨ True) → ((p3 ∧ (p2 → p3)) ∧ False)) → (True ∧ (p1 ∨ p4))) ∧ False) ∨ (False → p1))) ∨ ((p1 ∧ p4) ∧ p4)) ∨ p5) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340665455428330989953012456156 : (p2 → ((p1 → (p5 ∨ (((((p4 ∨ False) ∨ p3) → ((((p5 ∧ True) → ((False ∧ p2) ∧ True)) → (True → p3)) ∨ p1)) ∨ p4) ∨ True))) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52675764945657664533561590651 : (((p1 ∨ (p5 ∧ (p1 ∧ (p2 ∨ ((p1 → p5) ∨ (True ∧ (False → p3))))))) ∨ ((((p4 ∧ False) ∨ p3) ∧ (True → p2)) ∨ (p1 → p1))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89359292858517793970359405043 : (((True → (False ∧ p1)) ∧ ((((p2 → p1) → (p4 → ((p1 ∨ p4) → p3))) ∨ (p3 ∧ True)) ∧ (p1 → (((p3 → True) → p2) ∨ False)))) → p5) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645830401124848142190565893161 : ((((p5 ∨ (p1 → ((((p3 ∨ ((p1 ∧ p1) ∨ p4)) → p1) ∨ (True → (p3 ∨ p4))) → ((p2 → p1) ∧ ((p1 → p5) ∨ False))))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190642419871019505620382975695 : (((False ∨ ((p4 ∧ p1) ∨ (p3 → (False → p2)))) → p1) ∨ ((True ∧ p5) → ((((True ∧ ((p1 → p5) → (p3 ∨ p3))) ∧ p4) ∨ False) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h10 : (p1 → p5) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h12 := h7 h10
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134509284994479391906055517224 : (((((p5 → p3) ∨ ((False → (p4 → (p4 ∧ (True ∨ (False ∨ (p3 → p2)))))) ∧ (p3 ∨ (True ∧ p5)))) ∨ p4) → False) ∨ ((p1 → True) ∧ True)) := by
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
theorem thm_5_vars_729280523495928484856394223101 : (((((True ∧ p3) ∨ p1) → ((((p2 ∧ (p3 → (((p1 ∨ (p1 → p4)) ∧ p3) → ((False ∧ p2) ∧ p1)))) ∨ p5) ∨ p4) ∨ (p2 → True))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263387274856638619693565867263 : (True ∧ ((((True → p5) → ((p3 → p1) ∨ ((p3 ∨ ((p5 ∨ p3) ∧ ((p5 → True) → p2))) → p5))) ∧ (p3 ∧ p3)) ∨ ((False ∧ p3) → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_767997667626688039160020761752 : (((p5 ∧ ((p4 → ((((((p4 ∧ (((True → False) → p5) ∧ (False ∧ p1))) ∧ p5) ∧ p5) ∧ True) → (p3 ∨ (p1 ∧ p4))) ∨ p4)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133532540261746381813239677477 : ((((((((True → p3) ∨ p5) ∨ p3) → False) ∧ (p3 → ((((p5 ∧ p3) ∨ p1) ∧ p1) ∧ (False → p1)))) ∧ p1) ∧ p5) ∨ (p5 → (p5 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208964690161761444142163585449 : ((True ∨ ((True ∨ True) ∨ (False → p2))) → ((p2 ∨ p5) ∨ (((p5 ∨ p4) → (p3 ∨ (p1 → p1))) ∨ (p3 ∨ ((p1 → p3) → (p5 ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
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
          -- Implications on the right can always be decomposed.
          intro h13
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h15
          -- One of the premise coincides with the conclusion.
          exact h15
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h17
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h19
          -- One of the premise coincides with the conclusion.
          exact h19
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h21
          -- One of the premise coincides with the conclusion.
          exact h21
    case inr h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h23
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h25
        -- One of the premise coincides with the conclusion.
        exact h25
      case inr h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h27
        -- One of the premise coincides with the conclusion.
        exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114393789039598386375367599072 : ((((p1 ∨ (((p5 ∨ (p5 → (p2 ∨ p3))) → (p1 ∨ p2)) ∧ p5)) ∨ ((p3 ∨ p1) ∨ True)) ∨ ((p3 ∧ (p5 ∨ p4)) ∧ p4)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330988949624701864307090626922 : (True → (p5 → ((((p4 → True) ∧ p1) → ((p3 ∨ True) → False)) ∨ (False → ((False ∨ ((p1 ∧ p3) ∨ ((True → True) ∧ (p3 ∧ p1)))) ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606387847687987508924774650069 : ((((((((p1 ∧ True) → (p4 ∧ (p1 ∧ (p4 ∨ p5)))) ∨ ((((p3 → (p4 ∨ p4)) → p2) ∧ (p5 ∧ p5)) ∨ True)) ∨ p3) ∧ p2) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_118266042239700588051880982485 : ((p1 ∨ (((p1 ∧ (p5 ∨ (p4 ∨ False))) → ((p3 ∧ True) ∧ True)) → (((p1 ∨ (((p1 → p5) ∧ p3) ∨ True)) → False) ∧ p3))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756812198013538931608652068677 : (((p1 ∧ (((p4 → (((p1 ∨ p1) ∧ False) ∨ False)) ∧ (False → p5)) → (((False → (((p2 → (p3 ∧ p5)) ∧ False) ∧ p5)) ∧ p5) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249272736224233232033542448028 : ((p4 ∨ p4) ∨ (False ∨ (((p3 → (((True ∨ False) → (p1 → p5)) ∧ p4)) ∨ p4) → (((p5 ∨ ((False → p1) ∨ (p1 ∨ True))) ∨ p5) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115420395219315487151705727341 : ((((p1 ∧ (((True ∨ p1) → p2) → p5)) ∧ p2) ∨ (False ∧ (p2 ∧ (p3 ∧ ((p1 → ((p4 ∧ p2) → (p1 → p4))) ∧ p1))))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63226952111265239807690136915 : ((p5 ∧ ((False ∧ (p1 ∨ ((((((p4 ∧ True) ∧ p5) → False) ∧ p4) ∧ p3) ∧ p1))) ∧ ((p2 ∨ True) → (p3 → (p3 ∨ (p3 → p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309402640430156490733315936181 : (p2 ∨ ((True → ((((p5 ∨ (p3 ∨ ((p1 ∨ p4) ∧ True))) ∨ (p3 → (True ∨ p4))) → ((p1 → (False ∨ p4)) ∧ p4)) ∧ False)) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186383712232344804658358700632 : (((False ∧ (((True → p2) ∧ True) → ((p3 ∧ p1) ∧ p3))) → p3) → (p2 → ((p5 ∨ ((p3 ∨ p5) → (p3 → p4))) ∨ (p4 → (p3 ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117396490894462651148146175282 : ((p1 ∧ (((p1 ∧ (p1 ∨ (p4 → (False ∨ p4)))) ∨ ((p2 ∨ (True ∨ p4)) ∧ ((p3 ∨ (p5 → (p4 ∨ p3))) ∧ p1))) ∨ p3)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346607967236970381680693714046 : (p3 → ((((p2 → p2) → ((((p4 ∧ p4) ∨ True) → ((p1 ∨ p4) → (p1 ∨ p1))) ∧ p3)) ∨ ((p5 ∨ p2) → p1)) ∨ ((True ∧ False) → False))) := by
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
theorem thm_5_vars_178928247473512531420519000820 : (((p4 → p4) ∧ (((((p1 ∨ (p2 ∨ p2)) ∨ p5) ∨ True) → False) → p4)) ∨ ((p5 ∨ p2) ∧ (p5 ∧ (((p2 ∧ True) ∧ (False ∧ p2)) → p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((p1 ∨ (p2 ∨ p2)) ∨ p5) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318551993138612792193310947674 : (p4 ∨ (((p1 → (False ∧ (((p4 ∧ (p1 ∧ (p2 ∨ True))) → p2) ∧ ((p4 → ((True ∨ p3) → (p1 → False))) → False)))) ∧ p5) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260782144618827561289908700029 : ((p3 → p5) → ((True → (p4 ∧ ((((p1 ∨ p4) ∨ (True ∨ p3)) ∨ (p5 ∧ p2)) ∧ (((True ∧ p5) ∧ (p5 ∧ False)) ∧ True)))) → (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246245819662198121970807642070 : ((p4 ∧ p3) ∨ (p5 → ((((False ∧ p4) ∨ ((p3 ∧ p3) → ((p2 ∧ ((p5 → p3) ∨ p3)) ∨ p3))) ∧ p5) ∨ (p1 ∨ ((p2 ∧ True) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158652705788113319023152935590 : ((p1 ∧ ((p1 → p2) ∧ (False ∧ (p3 ∧ ((((p1 → ((p4 ∨ p1) ∨ p3)) ∧ False) ∨ False) ∨ False))))) ∨ ((((p2 ∧ p4) → p3) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245313680046485517209502284231 : ((p2 ∧ p2) ∨ ((p2 → (p5 ∨ p5)) → ((True → ((((p3 ∨ p1) ∨ (p5 ∨ (False → p5))) ∧ ((p3 ∨ p4) ∧ p3)) ∧ (p2 ∧ p3))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615858221278206020855298188309 : (((((((p4 ∨ (p2 ∧ p2)) ∧ p1) ∨ (False ∧ ((p1 → p1) ∧ (p4 ∧ p3)))) ∨ (p4 ∨ (True ∧ ((p1 ∧ (True ∨ p2)) ∨ True)))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_118701849197655524262765120069 : ((p5 ∨ ((((((p1 → True) ∧ p2) ∨ (False ∨ ((p3 → ((p5 → True) ∧ p1)) ∨ (True ∨ p2)))) ∨ (p3 ∧ p4)) ∨ False) → p5)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668046817196064496192454376365 : ((((p5 ∨ ((p5 ∧ (p2 ∨ ((p1 ∨ ((True ∧ p5) ∧ p5)) → p3))) → ((p4 ∨ (False ∨ p2)) ∨ (p1 → False)))) ∧ (p2 ∨ (False ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760607546729935078512881317019 : (((p2 ∧ (p4 ∧ ((p3 → (True ∨ ((p3 → (((p3 ∨ ((p4 → p3) → False)) → p3) ∨ ((p2 ∧ p5) ∧ p2))) → (p3 → p5)))) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68854995364055146462975793493 : ((p4 → ((p2 ∧ p4) → ((((p5 ∨ True) → ((False ∨ (((p1 ∧ (True ∨ p5)) ∨ ((True ∧ p5) ∨ True)) ∧ p1)) ∨ True)) ∨ False) ∨ False))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658541650977298435111091414430 : ((((p2 ∨ (((((p2 ∨ False) → p4) ∨ p1) ∧ True) → (((False ∧ False) ∧ p1) ∨ (p3 ∧ (((p5 ∨ False) ∨ True) ∧ p5))))) ∨ (p3 → True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_621147662809106832159559929256 : (((((p5 → p2) → (False ∨ (((p1 → (p2 ∧ (True ∧ (((p4 ∧ True) → p4) ∧ (p2 → (p4 ∧ False)))))) → p1) → (p4 ∨ p3)))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_717668386261982064455845657589 : ((((((False ∧ False) ∧ p3) ∧ p1) ∨ ((p3 ∧ (p3 ∨ p2)) ∨ (((((p4 ∧ (True ∧ p5)) → False) ∧ (p4 ∨ p3)) → (False → p4)) ∨ False))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117072269524082187440778342835 : (((True → p2) → (p3 ∨ (p1 ∨ ((p3 ∨ (((p3 ∧ p2) ∧ p5) ∨ ((True → (p1 ∧ p2)) → (True → p2)))) ∧ (False → p4))))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60326847351686076710090778131 : (((p2 → True) → (p2 ∧ ((p2 ∨ (((p2 ∨ ((True ∨ (p4 ∨ (p4 ∨ p4))) → True)) ∨ p3) ∧ p5)) ∨ (False ∨ (False ∧ (p4 → p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49271410819376808334867031057 : (((p2 ∧ (p2 ∧ (p3 ∧ ((p4 ∨ p3) → (p2 ∨ ((p3 → p2) → (((p2 ∨ p4) ∨ p5) ∧ (p2 → True)))))))) ∨ (p2 → (p5 → p5))) ∨ p4) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246610168889699414333997287516 : ((p5 ∧ p2) ∨ (p5 → ((((p5 ∨ (p4 ∨ p2)) ∧ ((p2 → True) ∨ (p4 → (p5 → False)))) ∧ (p1 ∧ (p1 → p2))) ∨ (p3 ∨ (p2 ∨ p5))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_550038163777588384929069104842 : (((p1 ∨ (((False ∨ p1) ∨ ((p4 ∧ p1) → (p3 → ((((p5 ∧ (p5 ∨ (p5 → True))) ∨ (p3 ∨ (False ∨ p4))) ∧ True) ∨ True)))) ∨ p1)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690723408327905542297386656803 : ((((((p2 ∨ (((((p3 ∧ p1) → True) ∨ True) ∧ (p3 ∧ p3)) → p4)) ∧ False) → False) → ((p5 ∨ (p4 ∨ p3)) ∨ ((p1 ∨ False) → True))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745115926223380593856257664682 : ((((p4 ∧ p4) → ((((False → (p4 ∨ True)) → (((p5 ∧ ((p5 ∧ (p2 ∧ (p2 → (False → p5)))) → False)) → p2) ∨ p1)) ∨ True) ∨ p2)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313368581607493944838080129597 : (p3 ∨ ((p4 → (p4 ∧ (((((p3 ∨ True) ∨ p4) → True) → p5) ∨ (((p2 ∧ p3) ∧ ((p4 ∨ (p1 ∧ p1)) → p1)) ∨ (p2 → p4))))) ∨ p3)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603744563385682617440562338542 : ((((p4 ∨ ((((((p5 → p5) → ((True ∧ False) → p2)) ∨ False) ∨ p5) → (((p2 → p2) ∧ p4) → True)) → (p1 → (p2 → p4)))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67554688930466124943817395771 : ((p1 → ((True → (True ∨ p4)) → (p3 ∨ ((p5 ∧ (p4 ∨ ((p4 ∨ (((p5 → p5) → p1) ∨ p4)) ∧ True))) → (p3 ∨ (p3 → p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775689414114307769157942036372 : (((False ∨ (p2 ∨ ((p5 → (((p2 ∨ (p4 → ((True ∨ p1) ∧ p2))) ∨ (True → (p4 ∧ p3))) ∨ p4)) → ((p3 → p4) ∨ (True ∨ p5))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299486147282742747305612257477 : (False ∨ ((p2 → (((p2 ∧ (((True → p4) → p3) ∧ (p5 → ((p3 → p4) ∨ p1)))) ∨ (p1 → False)) → (((p5 ∨ False) ∧ p1) ∧ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111625424202324634799162238128 : (((((p1 → ((p2 ∧ (p1 ∧ p5)) ∨ (((False → p4) ∨ (((p3 ∧ False) ∨ False) ∧ p2)) ∧ p5))) ∨ (True → p5)) ∨ True) ∨ p1) ∨ (p3 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809989726415182323203945552479 : (((p5 → ((((p2 → (p2 → ((p1 → True) ∧ (p5 ∧ (p1 ∧ p2))))) ∧ (True → (p5 → (p4 → p5)))) ∨ p2) → ((p2 → p1) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118124766493709322615260355221 : ((False ∨ (((p4 → (p2 → ((((p4 ∧ (p2 ∨ p3)) → False) ∨ ((p1 ∨ (p1 ∧ p2)) → False)) ∧ p1))) ∨ p3) ∨ (p4 → p4))) ∨ (True → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63934352086624516359123152752 : ((False ∨ (((((((p5 ∧ p3) ∨ p2) ∧ (((p4 ∨ ((p5 → p3) ∧ False)) ∧ p5) → True)) ∧ False) ∧ True) ∧ (False → (False → p5))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150168420062117579308599049714 : ((p1 → ((p2 → (p1 → p3)) → ((p3 ∧ False) ∨ (((True ∨ (p5 → (p1 → p3))) → (p4 ∨ p3)) ∨ p1)))) ∨ ((p3 ∧ p2) ∧ (p4 ∨ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46834657106267171002152712583 : (((((p5 ∧ ((True ∧ (((p2 ∧ (p4 → p3)) → p3) ∧ p3)) → False)) ∧ (p3 ∧ ((p4 → (p3 ∨ False)) → p1))) ∧ False) ∨ (p3 → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113798133279943362403713539164 : ((((p5 → False) ∨ (p3 → (p3 → (((p4 → ((p5 ∨ (p2 ∨ p3)) ∨ p4)) → p3) ∨ (p2 → (p2 → p3)))))) → (p5 ∧ p5)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241476863149572024103943988901 : ((False → p2) ∧ ((((True → (((p1 ∨ False) ∨ ((p1 → p2) ∧ p1)) ∧ p1)) ∧ False) ∨ p2) ∨ ((p4 ∧ p2) → (False ∨ (p2 ∨ (p4 ∨ p5)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261464600280378575147514406620 : ((p5 → p2) → (((False ∨ (p1 ∧ p5)) ∧ p5) → ((((((p5 ∧ p4) ∨ p2) ∧ p2) → (((p3 ∨ p5) → True) ∧ False)) ∨ p1) ∧ (p5 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h2.left
  let h11 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h16 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h17 := h1 h16
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343034800319961981972170463484 : (p2 → (((False ∨ True) ∨ (False → p5)) → (((p3 ∨ ((((((p5 → ((p2 ∨ p4) ∧ p2)) → p4) ∧ p3) → p3) ∧ p2) ∧ p5)) ∨ p1) ∨ p2))) := by
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785901732069146308253179794462 : (((p4 ∨ (((p5 ∧ ((p3 ∨ p2) ∧ (p3 ∨ p5))) → ((((((p2 → p1) → False) ∧ (p2 → True)) → True) → p3) ∧ True)) ∧ (False ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650368430235734879104383941714 : ((((((((False ∨ (False → (p2 ∨ p1))) ∧ ((p3 ∨ False) ∧ False)) → p3) → p1) ∨ ((p3 ∨ False) ∧ ((p4 ∧ p4) ∧ p1))) ∧ (False ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639428400486303869940251264925 : (((((True → (p1 → (p2 → p1))) → ((((p2 → ((p5 → p3) ∧ ((True → p2) ∨ (p3 ∧ p1)))) → False) ∨ True) → (p3 ∧ p3))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339533509395230723121794937484 : (p1 → (False ∨ (p4 → ((((p2 → False) ∨ True) ∧ (p5 ∨ p5)) ∨ ((p5 ∨ (False ∨ ((((p1 ∧ p1) ∧ p2) → p5) ∧ False))) → (p2 ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200091501805968669097340714977 : ((((p1 ∧ p5) → True) ∧ ((p5 ∧ p4) → p1)) → (((((True ∧ p5) → (p3 ∧ ((p3 ∧ p5) ∧ p3))) ∨ (False ∨ (p2 → True))) → False) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (((True ∧ p5) → (p3 ∧ ((p3 ∧ p5) ∧ p3))) ∨ (False ∨ (p2 → True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h5
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217064412817094453148693230133 : ((((p1 → p5) ∧ p2) ∨ False) → (((p5 ∧ (((p1 ∨ (((False ∨ p2) → ((p1 → p3) → p4)) ∨ p1)) ∨ True) ∧ (False → p5))) → p5) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h14 =>
          -- One of the premise coincides with the conclusion.
          exact h6
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h16 =>
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231278900256755691807334685655 : (((p5 ∨ False) ∨ p4) → (p4 ∨ ((False ∨ ((p2 ∨ ((p2 ∨ (True ∨ (True ∨ (p3 ∨ p5)))) ∨ False)) ∨ p3)) ∧ (False ∨ (p5 ∨ (p4 ∨ p4)))))) := by
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_994254669992745304618706484736 : (((p5 ∧ ((p5 → (((p2 → (p2 → (p2 → (p4 ∨ ((((p3 → (True ∨ p1)) → (p1 ∧ False)) ∧ p1) ∧ p2))))) ∧ p4) ∧ False)) ∨ p4)) → p4) ∧ True) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655218691777864163190994445749 : (((((((((p2 → p3) → p1) → (p1 ∧ p5)) ∨ ((p3 ∧ (p4 ∧ (False ∧ p2))) → (False → False))) → p3) ∧ (p2 ∧ p1)) ∨ (p4 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344695358606657339397283525092 : (p2 → (p2 → (p1 ∨ (p4 ∨ (((((((p3 → True) → p1) → p1) → (p5 ∧ (False ∧ (p3 ∨ p4)))) → p4) ∧ (p2 → (False → p4))) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116165834462728592344214780578 : (((True → (p1 ∧ True)) ∧ ((((p3 → False) → (p5 → (p1 ∨ p2))) ∨ (((p1 ∨ p5) ∨ True) ∨ ((True → p4) → p4))) → False)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38507136290966892019906241184 : ((((p1 ∧ ((p3 → p3) ∧ (((p5 ∧ (p5 ∧ p2)) → False) → p4))) ∨ ((p3 → (p4 ∧ (p2 ∧ p2))) ∨ (p5 ∧ (p3 ∨ p1)))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342308779222495923472939434151 : (p2 → ((((p4 ∧ p3) → (True ∧ ((p2 ∨ (((p4 ∨ (p4 → p1)) → False) ∧ p3)) → p3))) ∧ p5) → (((p4 → (False ∨ False)) ∨ True) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_436644686521348987626671478136 : (((((p1 → False) ∧ (((False → ((False → (((p2 ∨ (p5 ∧ p5)) ∧ p5) ∨ p4)) ∧ (p5 ∧ p4))) ∧ True) ∨ (p5 ∨ False))) → (p1 → p4)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h12 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h13 := h3 h12
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304342930404168474723557190219 : (p1 ∨ (((((True ∨ (p2 ∧ p4)) ∨ (p3 ∧ p4)) ∨ (p5 ∨ p5)) ∧ (((((p3 ∨ p3) ∨ False) → False) → True) → (p1 ∧ (False ∨ p2)))) → p2)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h7 : ((((p3 ∨ p3) ∨ False) → False) → True) := by
          -- Implications on the right can always be decomposed.
          intro h8
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h9 := h3 h7
        -- We need to get the right conjuct of h9 based on <expert-advice>.
        let h10 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- One of the premise coincides with the conclusion.
          exact h12
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h19 : ((((p3 ∨ p3) ∨ False) → False) → True) := by
        -- Implications on the right can always be decomposed.
        intro h20
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h21 := h3 h19
      -- We need to get the right conjuct of h21 based on <expert-advice>.
      let h22 := h21.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- False on the left can always be used.
        apply False.elim h23
      case inr h24 =>
        -- One of the premise coincides with the conclusion.
        exact h24
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h26 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h27 : ((((p3 ∨ p3) ∨ False) → False) → True) := by
        -- Implications on the right can always be decomposed.
        intro h28
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h29 := h3 h27
      -- We need to get the right conjuct of h29 based on <expert-advice>.
      let h30 := h29.right
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- False on the left can always be used.
        apply False.elim h31
      case inr h32 =>
        -- One of the premise coincides with the conclusion.
        exact h32
    case inr h33 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h34 : ((((p3 ∨ p3) ∨ False) → False) → True) := by
        -- Implications on the right can always be decomposed.
        intro h35
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h36 := h3 h34
      -- We need to get the right conjuct of h36 based on <expert-advice>.
      let h37 := h36.right
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h38 =>
        -- False on the left can always be used.
        apply False.elim h38
      case inr h39 =>
        -- One of the premise coincides with the conclusion.
        exact h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124714731969695129934216421112 : ((((p2 → (True ∧ False)) ∧ p2) ∧ (False → (((p1 → (p2 ∨ (p1 ∧ (p4 ∧ p1)))) ∨ ((p5 ∨ (p4 → p1)) ∧ p4)) → p3))) → (True → p4)) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45678576585805237025561069117 : (((p5 ∨ (((p3 → ((p4 → p5) → False)) → (p3 ∧ p4)) ∧ ((p4 ∨ ((True ∧ p2) ∨ ((p1 ∧ p1) → (p5 → True)))) ∨ p3))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205623119613690289804574135015 : (((p1 ∧ p4) ∨ ((p5 ∨ False) ∨ p4)) ∨ ((((p3 → p4) → (p5 ∨ ((p2 ∧ p4) ∨ (p2 ∧ ((p1 ∧ p5) → p5))))) ∧ (p2 → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322616576109342891759250002527 : (p5 ∨ ((p5 → (((((p2 ∨ ((False → p1) ∧ (p3 ∨ ((True → p4) ∨ p4)))) → p3) ∨ p5) ∧ ((p2 ∨ (p4 → p5)) ∧ True)) ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228063725137979633931345435250 : ((p4 ∧ (p3 ∧ True)) ∨ (((((((p5 → False) ∨ (p1 → p5)) ∨ p2) ∧ True) ∧ p1) → (p4 ∨ p1)) ∧ ((True → (p4 → p3)) ∨ (False → p5)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h10
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140976916267589917064766931771 : ((((p5 → (((p3 ∨ (True → p1)) → p2) → False)) ∨ p1) → (p2 → (((False ∧ p2) ∨ p1) ∧ ((p3 ∧ p1) ∧ p3)))) → (p2 → (p2 ∧ True))) := by
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
theorem thm_5_vars_209045340314026368634399799185 : ((p1 ∨ ((p3 ∧ (p3 → True)) ∨ p5)) → ((False ∨ (True ∧ p1)) ∨ (((True ∨ p4) ∨ (True ∨ False)) ∨ (((p4 ∨ p3) → p4) ∨ (p2 ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
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
    case inr h7 =>
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
theorem thm_5_vars_191224058015297673414468178465 : (((p1 ∨ (True ∨ True)) → (((True → p3) → p4) → False)) ∨ ((p1 ∧ (((((p2 ∧ p5) → p1) ∨ (p2 → (False ∨ True))) ∧ p2) ∨ p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776757881474325504984277205438 : (((p1 ∨ ((((p4 ∨ p3) ∧ ((p3 ∨ ((p2 → p2) ∨ (p4 → (p3 ∨ p5)))) ∧ ((p4 ∧ p2) → p2))) ∧ (p2 → (p4 ∨ p1))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607845433504464112981109052162 : (((((p5 ∨ ((p4 → (((True → p4) ∨ ((False → p5) ∨ (p3 → p4))) ∨ ((((p2 ∨ p5) ∧ True) ∧ p1) ∧ p2))) → p2)) ∧ False) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_770022365827779628059513727255 : (((p5 ∧ (p2 → ((p3 → False) ∧ ((((p3 ∧ p4) ∨ False) ∨ False) ∨ (p1 ∧ (((p5 ∨ False) ∨ (p5 → p1)) → (p3 ∨ (p2 → p3)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199058179841528506420554511247 : ((((True → (p5 ∧ (p1 ∨ p4))) ∨ p4) ∧ p5) → (p2 ∨ ((p5 → (((p4 ∨ p3) ∨ (p2 ∧ (p2 ∧ p2))) ∨ True)) ∧ (p1 ∨ (p3 ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h13
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56597150567781293816732333710 : (((p3 → (False ∨ (p3 ∧ False))) → ((((p2 ∧ ((p3 → (p5 ∧ p1)) ∨ p2)) → p1) ∧ p1) ∨ (((p4 ∨ p3) ∨ p5) ∨ (p2 ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



