variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41787445626996127649742975586 : ((((((p2 ∨ False) → p1) → p2) → (((p2 ∨ False) ∨ False) ∨ ((p4 ∨ p4) ∧ (((p3 ∧ (p1 → p2)) ∨ (True ∨ p4)) → p2)))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638171851649287724114643714081 : ((((((((p5 → p2) ∧ p4) ∧ True) ∨ (p5 → False)) → ((((p5 ∧ False) ∧ False) ∧ p3) ∨ (True ∨ ((p2 → p3) → (p4 → False))))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644586820406833759901303983188 : ((((p1 ∨ ((((((p3 → p1) ∨ (((p3 → p5) ∧ p2) ∧ p5)) → (True ∨ True)) ∧ True) ∧ p1) → (((p1 ∧ True) → False) → False))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665642678565100980777484570924 : ((((((p3 ∧ p3) ∨ (p3 → ((True → p5) ∧ (False ∧ (((p5 ∨ (False → p5)) ∨ False) ∨ (True ∨ p5)))))) ∨ p1) ∧ (p2 ∧ (p3 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134362847507462374480322712426 : (((p1 ∨ ((((((((False ∧ p4) ∨ p4) → False) ∧ p5) → p5) ∧ p4) ∧ ((p5 ∨ False) ∧ p2)) ∧ (p5 ∧ p2))) ∨ p1) ∨ ((p3 ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232271678350728693719274424403 : (((p2 → p2) → p1) → (p1 ∧ ((p3 ∨ False) → ((p2 ∧ (((p3 ∧ (p3 ∨ (p2 ∨ (p4 → p5)))) ∨ p4) ∧ (p1 → False))) → (p4 ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h15 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h16 : p1 := by
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h17 : (p2 → p2) := by
            -- Implications on the right can always be decomposed.
            intro h18
            -- One of the premise coincides with the conclusion.
            exact h18
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h19 := h1 h17
          -- One of the premise coincides with the conclusion.
          exact h19
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h20 := h10 h16
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- False on the left can always be used.
        apply False.elim h21
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h24 =>
          -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
          have h25 : p1 := by
            -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
            have h26 : (p2 → p2) := by
              -- Implications on the right can always be decomposed.
              intro h27
              -- One of the premise coincides with the conclusion.
              exact h27
            -- We have shown the premise of h1, we can now drive its conclusion.
            let h28 := h1 h26
            -- One of the premise coincides with the conclusion.
            exact h28
          -- We have shown the premise of h10, we can now drive its conclusion.
          let h29 := h10 h25
          -- False on the left can always be used.
          apply False.elim h29
        case inr h30 =>
          -- False on the left can always be used.
          apply False.elim h30
      case inr h31 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h32 =>
          -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
          have h33 : p1 := by
            -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
            have h34 : (p2 → p2) := by
              -- Implications on the right can always be decomposed.
              intro h35
              -- One of the premise coincides with the conclusion.
              exact h35
            -- We have shown the premise of h1, we can now drive its conclusion.
            let h36 := h1 h34
            -- One of the premise coincides with the conclusion.
            exact h36
          -- We have shown the premise of h10, we can now drive its conclusion.
          let h37 := h10 h33
          -- False on the left can always be used.
          apply False.elim h37
        case inr h38 =>
          -- False on the left can always be used.
          apply False.elim h38
  case inr h39 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h40 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h39
    case inr h41 =>
      -- False on the left can always be used.
      apply False.elim h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244259979812638015843859241904 : ((False ∧ True) ∨ ((((False ∧ p2) ∨ (p5 → False)) ∨ (((p3 → p1) → False) ∨ (p2 ∨ (p1 → (p3 → ((p1 → False) → p3)))))) ∧ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60401505829799982432655404516 : (((p4 → True) → ((((((p2 ∧ p1) ∧ p1) ∨ False) ∧ (p4 → (p3 ∧ (True ∧ p1)))) ∨ (True → (((False ∧ p1) → p5) → True))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260404444179416175487589417278 : ((p3 → True) → (((((False ∨ ((False ∧ p1) → p2)) ∧ ((p4 ∨ p5) ∧ (p4 ∧ False))) ∨ False) ∨ (True ∨ (((p1 ∨ p1) → p2) ∨ p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589885564482842437246020671605 : ((((((False ∧ (p1 → (p4 ∧ ((True ∨ (((False → False) ∨ (p2 ∧ False)) ∧ (p1 ∧ p2))) ∨ p5)))) ∨ ((p3 ∨ p1) → True)) → False) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62431769463207858561627669897 : ((p3 ∧ (((p1 → (p1 ∨ p2)) ∧ p4) → ((True ∧ p1) → (((True → True) → p2) ∧ (p1 ∧ (p2 ∧ (p5 ∨ ((p1 → True) ∧ p3)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19958214009610063879514992449 : ((((((p2 ∨ (True ∨ p4)) → (False ∨ p2)) ∨ ((True ∨ p4) ∨ p5)) ∨ p3) ∧ (((p1 ∨ (False ∨ p3)) ∧ ((p3 ∧ p1) ∧ False)) → p3)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h3.left
      let h13 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38397384332127260926670372279 : ((((p1 ∧ ((p1 → (((p2 ∧ (p1 ∨ p2)) → (p1 ∧ False)) → False)) → (p2 → p4))) → ((((True ∧ p1) ∧ p1) → p3) → False)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206464410980649546722939974628 : ((p4 ∨ (p1 ∨ ((p1 → False) ∧ False))) ∨ (((p3 ∧ p1) ∨ (p4 ∨ (p5 → (p3 ∨ (True ∨ ((p2 → ((False ∨ p2) ∧ p1)) ∨ p1)))))) ∨ False)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658241440457890022646407600728 : ((((p5 ∧ ((True → False) ∧ (((p4 ∨ False) ∧ (((((True ∧ p4) ∨ (p4 → p5)) ∨ p3) ∨ False) → (p4 → p1))) → p2))) ∨ (p3 ∨ True)) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57354507010108889018281346755 : (((p3 ∧ (False ∨ p3)) ∨ (p3 → ((False → p3) → (False ∨ (p2 → (p2 → ((p1 → ((p4 ∨ ((False → True) ∧ p2)) → p5)) → p5))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219417258214559986720034026285 : ((p4 ∨ ((p1 ∧ p2) ∧ p5)) → ((((True ∨ p5) → (True → ((p3 → p1) ∧ p1))) ∨ p2) ∨ ((True ∧ ((p5 ∨ (p5 ∧ True)) ∨ True)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179127318227006922400266774631 : ((p1 ∧ ((p5 ∨ ((((p4 ∨ p3) ∧ p4) → p5) ∨ p3)) ∨ (False → p1))) ∨ ((p3 ∧ (((p3 ∨ p3) ∧ (False ∧ p3)) ∧ (True ∧ p2))) → p5)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h7.left
    let h13 := h7.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110716951753797999437528612115 : (((((p5 ∨ (p1 → (False ∧ (((p3 → ((p2 ∧ p5) ∧ p2)) ∨ ((p2 ∨ p5) ∨ (p1 → p4))) → p4)))) → False) ∧ p4) ∧ p3) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784058441756451187045437966213 : (((p3 ∨ ((False ∧ p5) ∨ ((((p3 ∧ ((True ∨ p3) ∨ p2)) ∨ (p2 ∨ (p2 ∧ ((p4 ∧ (p4 ∨ (p2 → p5))) ∧ p1)))) ∨ p3) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68447557873416712349832847276 : ((p3 → (False ∧ (((p4 → ((True ∨ (False → p5)) ∨ True)) → p1) → ((p2 ∨ ((((p1 ∧ p5) ∨ (False ∨ False)) ∨ p4) ∧ p5)) ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299361053511226057048275339811 : (False ∨ (((p3 ∨ p1) ∧ (p2 ∧ (p5 ∨ (p4 ∧ (False ∨ (((p5 → True) → ((p3 ∨ (p5 ∨ p4)) ∨ ((p1 ∧ p4) → p2))) ∧ p4)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709762087609174968640337514295 : ((((p1 → ((((p1 → False) → p4) ∨ p2) → False)) → (((p2 ∨ p1) → p3) ∧ ((((p2 ∧ False) ∨ (p4 ∨ True)) ∧ (p5 ∨ p3)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148392735345038031867145179421 : (((True ∧ (p4 ∨ ((True ∧ p2) ∨ (p4 ∨ ((True → (True → p2)) ∧ p4))))) ∨ (p1 ∧ ((p2 ∨ p5) → p2))) ∨ ((p2 → (p2 → True)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802107566646256996383871955118 : (((p2 → (False ∧ ((((((False ∨ p5) → (False ∨ p3)) → (p5 ∧ (((p2 → False) ∧ (p5 → p1)) ∨ p1))) → (p1 → p2)) ∨ p4) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612241949185237890711514297283 : ((((((p3 ∧ (p5 ∨ p4)) → ((p5 ∨ p5) ∧ ((p1 ∨ p2) → ((((True ∧ True) → p2) → p1) ∧ (True ∧ p3))))) ∧ (p4 ∧ p5)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_689163175435694088906294344148 : ((((((p5 ∧ ((((p3 ∨ True) ∨ (True ∧ (p1 ∨ p2))) ∧ True) ∨ p2)) → p3) → p4) ∨ (((p4 → True) ∨ True) ∨ ((True ∨ p5) → p1))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258767177382650421919408228168 : ((True → False) → ((p4 ∨ ((((((p3 ∨ False) ∨ (((True ∨ p5) ∨ (p1 ∧ p3)) ∧ (p2 → False))) ∨ False) → p5) ∧ (p5 ∨ p2)) ∧ p5)) ∨ p4)) := by
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
theorem thm_5_vars_750580105762044555267510342361 : (((True ∧ (((p1 ∨ (p4 ∨ ((((p2 ∧ p5) ∧ p3) ∧ (p3 → ((p3 → p3) → p2))) ∨ p4))) ∨ p4) → ((p5 ∧ (p5 ∧ True)) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_386159164357558570059246015214 : ((((((((((p5 → False) ∧ p4) ∧ (p3 ∧ p5)) ∨ False) ∨ (p4 → p5)) ∨ (True → ((p4 ∨ (False ∨ p2)) → True))) ∨ (False → p1)) ∨ False) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134838926221432313150252050166 : (((p3 ∨ ((False ∧ (True ∧ (((p5 → (p4 ∨ p3)) ∨ ((False ∨ p4) ∧ p3)) → p4))) → ((p1 → p5) → False))) → False) ∨ (p4 ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186109928086292714582126485332 : (((((p2 → (p4 → (p3 ∨ p1))) → p3) → (False ∧ p1)) ∨ p3) → ((((True ∨ True) → (True ∨ True)) → False) ∨ (p4 → (p2 → (p4 ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311036597078708159204178953752 : (p2 ∨ ((p3 ∧ True) ∨ ((False ∨ ((p2 → (True ∧ True)) ∨ p3)) → (p5 ∨ ((False ∨ ((True ∨ (False ∨ False)) → (True → p2))) ∨ (True ∨ p4)))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738673524628206659942135019509 : ((((p2 ∧ p1) ∨ ((p1 → ((p3 → ((p2 ∧ (p4 → True)) ∧ p3)) ∧ ((p4 → (p5 ∨ True)) ∨ False))) → (p4 → (p5 ∧ (p3 ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64438918689130051392087593676 : ((p1 ∨ (((((((p1 → True) ∧ (p1 → p5)) → p4) ∧ True) → ((((True ∨ p3) → p2) ∧ p1) ∨ p3)) → (p4 ∧ p5)) ∨ (p4 → p4))) ∨ p4) := by
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
theorem thm_5_vars_39834506282533804966853962422 : (((p1 → ((((True ∧ p5) ∨ p2) → (False → (((p5 ∨ (True ∧ ((((p5 ∨ p5) ∧ p3) ∨ p5) → p5))) → p1) → p3))) → p4)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691855132341215113372274317725 : ((((True → (p5 → ((p3 ∨ p4) → ((p3 ∨ ((p1 ∧ (p2 → p3)) ∧ p1)) ∨ True)))) → ((False ∧ ((p4 → p2) → (p1 ∨ True))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263561919277106068430054463161 : (True ∧ (((p2 ∧ ((((False ∨ (p1 ∧ (p3 → False))) ∧ (False → p1)) → False) ∨ (p5 ∨ p5))) ∨ (p2 → True)) ∨ (p5 ∨ ((p1 ∨ p2) ∧ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308462775722134951328338847024 : (p2 ∨ ((((p2 ∧ (p3 ∨ (p1 ∨ p2))) → (p1 ∧ (True → (p5 ∨ (True ∨ ((False ∨ (False → (p2 → p2))) → p1)))))) ∨ (p4 ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2545876123739534268627869535 : (((False ∨ (p3 ∧ (p4 ∨ (p2 ∨ False)))) ∨ p5) ∨ (((False ∨ p5) → p5) ∨ (p3 ∨ (((p4 ∨ ((True ∨ p1) ∨ True)) ∨ p2) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192671153958889668807476335236 : ((((p3 ∧ (p5 ∨ (p4 ∨ (p5 ∧ p4)))) → p3) → False) → ((((p2 ∨ True) ∨ p4) ∧ ((p1 ∨ p4) ∨ (((p5 ∧ p4) ∨ p3) ∨ p1))) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∧ (p5 ∨ (p4 ∨ (p5 ∧ p4)))) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- One of the premise coincides with the conclusion.
        exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h2
  -- False on the left can always be used.
  apply False.elim h12
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h13 : ((p3 ∧ (p5 ∨ (p4 ∨ (p5 ∧ p4)))) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- One of the premise coincides with the conclusion.
        exact h15
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h23 := h1 h13
  -- False on the left can always be used.
  apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320030152256011494112821783337 : (p4 ∨ (((p3 → p2) ∨ p3) ∨ (p2 ∨ ((False ∨ (((p1 ∨ (p3 ∨ p3)) → (p4 ∧ p3)) → (p1 ∨ ((p3 → True) ∧ (p2 ∧ True))))) ∨ True)))) := by
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
theorem thm_5_vars_207947556387188404041597358643 : (((p1 → (p1 → p1)) ∧ (p2 → p2)) → (p2 → (((p2 ∧ False) ∧ (p4 → (((True → (True ∨ (p3 → p5))) ∧ True) → p1))) ∨ (False → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245282974419959184109916094428 : ((p2 ∧ p2) ∨ (((False ∨ (True ∧ ((p4 → (p1 → (p1 → p4))) ∧ (p1 ∨ p2)))) → (((((p2 ∨ p5) → p2) → False) ∨ False) → p1)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h12 : ((p2 ∨ p5) → p2) := by
          -- Implications on the right can always be decomposed.
          intro h13
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- One of the premise coincides with the conclusion.
            exact h14
          case inr h15 =>
            -- One of the premise coincides with the conclusion.
            exact h11
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h16 := h3 h12
        -- False on the left can always be used.
        apply False.elim h16
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60186343072776346809265963577 : (((p5 ∨ p2) → (p3 ∧ (((p1 ∧ ((p3 ∧ (((p1 ∧ p3) → p3) ∧ True)) ∨ True)) ∨ (p4 ∨ p4)) ∧ (((p4 ∨ p3) ∧ p1) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87766154963496640058204774279 : ((((((p1 ∧ p5) ∨ p3) ∨ False) ∨ True) → (p1 ∧ (False → (((p2 → ((p3 → (((True ∨ p4) ∧ p2) ∨ p1)) ∨ p3)) → p3) ∧ False)))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 ∧ p5) ∨ p3) ∨ False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213297494139986063099714709284 : ((((p5 → p2) → p5) ∧ p4) ∨ ((p5 ∨ ((True ∧ (((((False ∨ p1) → p5) ∧ p3) → p2) ∧ False)) → p4)) ∨ (True → (True ∧ (False → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137868309127446504967159292140 : ((p3 ∨ (True → ((((False ∧ p2) ∨ p4) ∧ (p3 ∧ ((p4 ∨ (p2 ∨ ((p5 ∧ (True ∨ p5)) ∧ p5))) ∨ p3))) ∨ True))) ∨ ((p3 → p1) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748206246820127956535884674192 : ((((p1 → p5) → (((p5 → p5) → False) ∨ ((((p1 → True) ∧ True) ∧ True) ∨ ((True ∨ ((False ∨ p5) → ((p3 ∧ p3) ∧ p3))) ∧ p5)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774516049548890155520513591574 : (((False ∨ (((False ∨ (p4 → (p2 ∧ ((True ∧ (p3 → False)) ∧ (p1 ∧ False))))) → p5) ∨ ((((p4 → False) → True) ∧ p1) → (p5 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191632661630739744449866202383 : ((p4 ∧ ((((False ∨ (p1 ∧ True)) ∧ p3) ∨ False) ∨ True)) ∨ (p3 ∨ (True ∨ (((((True ∨ (p4 → p1)) ∧ True) ∧ (False ∧ True)) ∧ True) ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341061519021685947573006385691 : (p2 → ((p3 ∨ (True ∧ (True ∧ ((p3 ∨ ((p3 ∧ True) → (p2 → (((p2 ∧ p4) → p3) ∨ p3)))) ∧ (((p5 ∨ False) ∧ p3) ∧ False))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191172192861069058076620266884 : (((p3 ∨ (False ∧ p2)) ∨ ((p3 → (p3 ∨ False)) ∧ p1)) ∨ ((False ∧ (p4 → p5)) ∨ ((p4 ∧ p1) → ((((p2 ∧ p4) ∨ False) ∧ p1) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_149283580082031737060648432587 : (((p2 → p4) ∨ (((((p3 → (p3 ∧ (p3 → (True ∨ (p4 ∨ p4))))) ∨ p3) → p3) ∨ False) ∨ (p1 ∧ p5))) ∨ (((p2 ∧ True) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136243012085706625327874797900 : (((p1 ∧ ((p3 → (p5 → p5)) ∧ True)) ∨ ((p4 → (p1 ∧ p4)) ∨ (p4 ∧ (((p4 → True) ∨ p2) ∧ (True → p1))))) ∨ ((p5 ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341732848744363180634312525145 : (p2 → (((p1 ∧ False) ∧ ((False ∧ (p3 ∧ p3)) ∨ (((p4 ∧ p4) ∧ ((p2 ∨ True) ∧ (p2 → True))) ∨ ((False ∧ p3) ∨ p3)))) ∨ (True ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117047957197381433212876073248 : (((p4 ∨ p1) → (((p5 ∨ (((((p4 ∨ True) ∨ p4) → p1) → False) → (p4 ∧ p3))) ∨ p3) → ((p5 ∧ (False ∨ p4)) ∨ p1))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117827328070959650525373675397 : ((p4 ∧ (p4 ∧ ((((p3 ∨ p5) ∨ p2) ∧ (p3 ∨ (p5 ∧ ((False → p3) → (p5 → p3))))) → (p4 ∧ (p5 → (p5 ∨ p1)))))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215588065568335185022923566162 : ((p5 ∧ (p3 ∧ (p1 → p5))) ∨ ((p3 ∧ (False ∧ p5)) ∨ (True ∨ (p4 ∧ ((((p5 ∨ True) ∧ (p1 → False)) → ((False ∧ p3) ∧ p5)) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338280132488200641428336930363 : (p1 → (((p5 → p2) ∨ ((p1 → p5) ∨ p3)) → (p3 → ((((p5 → (((False ∨ p5) ∧ False) ∧ False)) ∨ p1) ∧ (p3 ∧ p1)) ∨ (p5 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h7
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252148137913161959203252054187 : ((p4 → p3) ∨ ((p3 → ((p5 ∧ p2) ∧ (((p3 ∨ p4) → False) ∨ (((p3 → ((p2 ∧ p3) ∧ (True → True))) ∧ (True ∧ True)) → p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324552900116158735261766197868 : (p5 ∨ ((p4 ∧ (p2 → (True ∨ True))) → ((((((p5 → p5) ∨ ((p3 → False) → p2)) ∧ p1) ∨ True) ∨ (True ∧ p2)) → ((p5 ∧ False) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h1.left
        let h9 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h1.left
        let h12 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h1.left
      let h15 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h1.left
    let h20 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205234907363092949112417640589 : ((((p5 → p3) ∧ False) ∨ (p5 ∨ p1)) ∨ ((p2 → (False ∨ (((p1 ∨ True) → False) → (((p3 ∨ p5) ∨ True) → (p1 ∧ (True → False)))))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : (p1 ∨ True) := by
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
      have h9 : (p1 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h9
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : (p1 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h12
    -- False on the left can always be used.
    apply False.elim h13
  -- Implications on the right can always be decomposed.
  intro h14
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h17 : (p1 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h18 := h2 h17
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h20 : (p1 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h21 := h2 h20
      -- False on the left can always be used.
      apply False.elim h21
  case inr h22 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h23 : (p1 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h24 := h2 h23
    -- False on the left can always be used.
    apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179141118154541409573784622825 : ((p1 ∧ (p2 ∨ (((((p5 ∨ p5) → p1) ∨ (p4 ∧ p5)) ∨ p1) ∨ True))) ∨ (p1 → (((False ∨ p1) ∧ p1) → ((p4 → (p4 → True)) ∨ True)))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46680163633520348589517088852 : (((p2 ∨ (((p3 ∧ ((p2 ∨ p3) → False)) ∧ (False → (((p4 ∨ (p1 ∧ (p4 ∨ p3))) ∨ p5) ∨ (False ∧ False)))) ∨ True)) ∧ (False ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213405376935373320795147189944 : (((p1 ∨ (p5 ∨ p2)) ∧ p3) ∨ (p2 ∨ ((False ∨ True) ∨ (((p2 ∨ (True → (True → p1))) → (p1 → (p5 ∧ p1))) → ((p4 → p5) → True))))) := by
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
theorem thm_5_vars_47045774216226106388748386285 : (((((p4 ∧ p5) ∨ (True → ((p4 ∨ ((((p4 ∨ p1) ∧ (False ∧ p3)) → True) → (p4 ∧ True))) → p1))) ∧ (p4 → False)) ∨ (True ∨ p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57098437775333769901544328561 : ((((p5 ∧ p2) ∧ p4) ∨ ((((p5 → False) ∨ True) → p3) ∨ ((False ∨ p3) → ((False → p5) ∧ (((p5 → p4) ∨ p3) ∧ (False → p5)))))) ∨ p4) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_95545779246213330393497150345 : ((p5 ∧ (((p3 ∨ (p2 ∧ (p5 ∧ (((p3 → (p3 ∨ p2)) ∧ True) → p3)))) ∧ (False → (False → (False ∧ p2)))) ∧ (p1 ∨ (p5 → False)))) → p3) := by
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
    cases h5
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h16 =>
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h17 : ((p3 → (p3 ∨ p2)) ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h18
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h19 := h15 h17
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h21 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h22 := h20 h21
      -- False on the left can always be used.
      apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133687466131149087538649014432 : (((((p3 → ((((p5 ∧ ((p3 → p5) ∧ False)) ∧ (p5 ∨ False)) ∨ p4) → True)) → p5) ∨ (p1 ∧ (p1 ∨ p2))) ∧ p5) ∨ (p1 → (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53889670942181770773155423209 : (((True ∧ (p3 ∨ ((p5 ∧ (p4 → (True ∧ p5))) → p2))) ∨ ((False ∨ (p3 ∨ (True ∧ (False ∨ (p4 → (False → (p2 ∨ p4))))))) ∨ p4)) ∨ p3) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755005692877638224055824121618 : (((False ∧ (True → ((True ∧ ((((p3 ∧ p3) ∧ p4) ∧ (False ∨ (((p5 → (p5 ∨ p4)) ∨ ((p1 ∨ p4) → False)) → p1))) ∧ False)) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138260832768497224971169341491 : ((p2 → (p1 ∨ ((False ∨ ((p4 ∧ ((True ∧ p4) ∨ (p3 → ((True ∧ p5) ∨ True)))) ∨ p2)) ∧ ((True ∨ p1) ∨ p1)))) ∨ ((p1 ∨ p5) ∨ False)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180227346635041903701338982489 : (((False ∧ ((((p5 ∨ ((p4 ∧ True) ∧ p3)) ∨ p4) ∨ p3) → p4)) → p1) → (p3 ∨ (((True ∧ (p1 → p4)) → False) ∨ ((p5 ∨ False) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42303718519603007495589563086 : (((p2 ∧ (((((False → ((p1 ∨ p3) → p5)) ∧ ((p1 ∧ p4) ∨ (p4 → (True ∧ p3)))) → p5) ∨ True) ∨ ((p3 ∧ False) ∧ p1))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767231710113583149131808669768 : (((p5 ∧ ((((p3 → ((p3 ∧ p5) ∨ (((False ∨ (p1 ∨ p2)) ∨ p3) ∨ (p2 → ((p1 ∨ True) → (p1 ∨ False)))))) ∧ p4) → p3) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664103163880485111719260846389 : ((((True ∨ ((p5 ∨ (p3 ∨ p3)) → (((p3 ∨ (p3 ∨ True)) → (p3 ∨ (p4 ∨ p5))) ∨ ((True ∨ (p3 ∧ p1)) ∨ p4)))) → (p3 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200651582092559738854205900718 : ((p1 ∧ ((p1 ∧ (True → (p5 ∧ False))) ∨ False)) → ((p3 ∧ p1) → (((p2 ∨ p3) ∨ (p4 ∨ p4)) → ((p3 ∧ (p4 → False)) ∧ (p1 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h2.left
      let h7 := h2.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h1.left
      let h9 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h2.left
      let h16 := h2.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h1.left
      let h18 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h22 =>
        -- False on the left can always be used.
        apply False.elim h22
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h2.left
      let h26 := h2.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h1.left
      let h28 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- One of the premise coincides with the conclusion.
        exact h25
      case inr h32 =>
        -- False on the left can always be used.
        apply False.elim h32
    case inr h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h2.left
      let h35 := h2.right
      -- Conjunctions on the left can always be decomposed.
      let h36 := h1.left
      let h37 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h38 =>
        -- Conjunctions on the left can always be decomposed.
        let h39 := h38.left
        let h40 := h38.right
        -- One of the premise coincides with the conclusion.
        exact h34
      case inr h41 =>
        -- False on the left can always be used.
        apply False.elim h41
  -- Implications on the right can always be decomposed.
  intro h42
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h43 =>
    -- Disjunctions on the left can always be decomposed.
    cases h43
    case inl h44 =>
      -- Conjunctions on the left can always be decomposed.
      let h45 := h2.left
      let h46 := h2.right
      -- Conjunctions on the left can always be decomposed.
      let h47 := h1.left
      let h48 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h48
      case inl h49 =>
        -- Conjunctions on the left can always be decomposed.
        let h50 := h49.left
        let h51 := h49.right
        -- We want to use the implication h51 based on <expert-advice>. So we show its premise.
        have h52 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h51, we can now drive its conclusion.
        let h53 := h51 h52
        -- We need to get the right conjuct of h53 based on <expert-advice>.
        let h54 := h53.right
        -- False on the left can always be used.
        apply False.elim h54
      case inr h55 =>
        -- False on the left can always be used.
        apply False.elim h55
    case inr h56 =>
      -- Conjunctions on the left can always be decomposed.
      let h57 := h2.left
      let h58 := h2.right
      -- Conjunctions on the left can always be decomposed.
      let h59 := h1.left
      let h60 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h60
      case inl h61 =>
        -- Conjunctions on the left can always be decomposed.
        let h62 := h61.left
        let h63 := h61.right
        -- We want to use the implication h63 based on <expert-advice>. So we show its premise.
        have h64 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h63, we can now drive its conclusion.
        let h65 := h63 h64
        -- We need to get the right conjuct of h65 based on <expert-advice>.
        let h66 := h65.right
        -- False on the left can always be used.
        apply False.elim h66
      case inr h67 =>
        -- False on the left can always be used.
        apply False.elim h67
  case inr h68 =>
    -- Disjunctions on the left can always be decomposed.
    cases h68
    case inl h69 =>
      -- Conjunctions on the left can always be decomposed.
      let h70 := h2.left
      let h71 := h2.right
      -- Conjunctions on the left can always be decomposed.
      let h72 := h1.left
      let h73 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h73
      case inl h74 =>
        -- Conjunctions on the left can always be decomposed.
        let h75 := h74.left
        let h76 := h74.right
        -- We want to use the implication h76 based on <expert-advice>. So we show its premise.
        have h77 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h76, we can now drive its conclusion.
        let h78 := h76 h77
        -- We need to get the right conjuct of h78 based on <expert-advice>.
        let h79 := h78.right
        -- False on the left can always be used.
        apply False.elim h79
      case inr h80 =>
        -- False on the left can always be used.
        apply False.elim h80
    case inr h81 =>
      -- Conjunctions on the left can always be decomposed.
      let h82 := h2.left
      let h83 := h2.right
      -- Conjunctions on the left can always be decomposed.
      let h84 := h1.left
      let h85 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h85
      case inl h86 =>
        -- Conjunctions on the left can always be decomposed.
        let h87 := h86.left
        let h88 := h86.right
        -- We want to use the implication h88 based on <expert-advice>. So we show its premise.
        have h89 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h88, we can now drive its conclusion.
        let h90 := h88 h89
        -- We need to get the right conjuct of h90 based on <expert-advice>.
        let h91 := h90.right
        -- False on the left can always be used.
        apply False.elim h91
      case inr h92 =>
        -- False on the left can always be used.
        apply False.elim h92
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h93 =>
    -- Disjunctions on the left can always be decomposed.
    cases h93
    case inl h94 =>
      -- Conjunctions on the left can always be decomposed.
      let h95 := h2.left
      let h96 := h2.right
      -- Conjunctions on the left can always be decomposed.
      let h97 := h1.left
      let h98 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h98
      case inl h99 =>
        -- Conjunctions on the left can always be decomposed.
        let h100 := h99.left
        let h101 := h99.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h100
      case inr h102 =>
        -- False on the left can always be used.
        apply False.elim h102
    case inr h103 =>
      -- Conjunctions on the left can always be decomposed.
      let h104 := h2.left
      let h105 := h2.right
      -- Conjunctions on the left can always be decomposed.
      let h106 := h1.left
      let h107 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h107
      case inl h108 =>
        -- Conjunctions on the left can always be decomposed.
        let h109 := h108.left
        let h110 := h108.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h109
      case inr h111 =>
        -- False on the left can always be used.
        apply False.elim h111
  case inr h112 =>
    -- Disjunctions on the left can always be decomposed.
    cases h112
    case inl h113 =>
      -- Conjunctions on the left can always be decomposed.
      let h114 := h2.left
      let h115 := h2.right
      -- Conjunctions on the left can always be decomposed.
      let h116 := h1.left
      let h117 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h117
      case inl h118 =>
        -- Conjunctions on the left can always be decomposed.
        let h119 := h118.left
        let h120 := h118.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h119
      case inr h121 =>
        -- False on the left can always be used.
        apply False.elim h121
    case inr h122 =>
      -- Conjunctions on the left can always be decomposed.
      let h123 := h2.left
      let h124 := h2.right
      -- Conjunctions on the left can always be decomposed.
      let h125 := h1.left
      let h126 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h126
      case inl h127 =>
        -- Conjunctions on the left can always be decomposed.
        let h128 := h127.left
        let h129 := h127.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h128
      case inr h130 =>
        -- False on the left can always be used.
        apply False.elim h130



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714186154053586535389529541556 : (((((p2 → (p4 → (p4 → p1))) → p5) → ((((p2 → p3) → (((p4 ∧ (p1 ∨ p3)) → p3) ∧ p4)) ∧ (p2 ∨ p2)) → (p5 ∨ True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37510250953809906331309051081 : (((((True → p1) ∨ ((p3 ∨ (((p2 ∧ p2) ∨ p1) → (((p1 ∨ (p2 ∨ p3)) → p5) ∨ (p5 ∧ (p4 ∧ p2))))) ∧ p2)) ∨ p5) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226328378594104867139379953290 : (((p5 ∨ p2) ∨ p2) ∨ ((p4 ∨ (((False ∧ ((p5 → ((False ∨ p1) → p2)) ∧ p2)) ∧ (True → ((p4 ∨ False) ∧ (p1 ∧ p3)))) ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353212290229933621994779259726 : (p4 → (p4 ∧ (p1 ∨ (((True → ((p1 → (p4 → (False ∨ ((p3 → ((False → True) ∧ p1)) ∨ p1)))) ∧ p1)) ∧ False) ∨ (p3 → (p1 ∨ p3)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48330313300846030299997856327 : (((p1 ∨ (p3 ∨ ((p5 ∨ (((p2 ∨ False) ∨ ((p4 ∧ True) ∨ ((p1 ∨ p4) ∨ (p2 ∧ True)))) → p3)) ∨ (p4 ∨ False)))) → (p4 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778509032730053343148428062925 : (((p1 ∨ (p5 ∧ ((p4 ∧ (((p3 ∧ p2) ∧ ((True → p5) ∧ p4)) → (p5 ∧ p5))) ∧ ((((p5 ∧ False) ∧ p5) ∧ p4) ∨ (p2 ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177940544037840257627843351250 : ((((p4 ∧ (p5 ∨ p1)) ∧ (False ∧ ((p1 → False) ∨ (p5 ∨ p4)))) ∨ True) ∨ ((((p1 ∧ (p2 ∧ p4)) ∨ (False ∧ p2)) ∧ p4) ∨ (p3 → p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111604039119616512840726248801 : ((((((p3 ∨ (p3 ∧ True)) ∨ ((p4 ∧ (((p3 ∧ (p3 ∨ p2)) → p3) → p1)) → ((True ∧ p4) → False))) ∧ p3) ∨ True) ∨ False) ∨ (p5 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192486745976440734214667346493 : (((((True ∨ False) ∨ True) ∨ (p3 → (p5 ∧ True))) ∨ p2) → (((p3 ∨ True) → p3) → ((p2 → p5) → (((p4 ∧ (p3 → p5)) ∨ p3) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h8 : (p3 ∨ True) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h9 := h2 h8
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h10 =>
          -- False on the left can always be used.
          apply False.elim h10
      case inr h11 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h12 : (p3 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h13 := h2 h12
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h14 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : (p3 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h16 := h2 h15
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h17 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h18 : (p3 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h19 := h2 h18
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323688015286170411856885347993 : (p5 ∨ ((p5 ∨ (True ∧ (((True ∧ ((p4 ∨ p4) ∧ (p3 → (p5 ∧ (p2 ∨ (p2 ∧ True)))))) ∨ True) ∨ p3))) ∨ ((p5 → (p1 ∨ p2)) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_23520497985022658192732616786 : (((False ∨ (False → (True ∨ p4))) ∧ ((((p4 → p1) → p3) → ((p3 ∨ ((p3 ∧ p2) → p3)) → p2)) ∨ ((True → (True ∨ False)) ∧ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199677210903953726018978390241 : ((((p3 → p2) ∨ (p2 → (p5 ∧ p5))) → False) → (((p5 → ((True ∧ ((p5 ∧ (p5 → p3)) ∨ p2)) ∧ (p3 → (p4 → False)))) ∨ p3) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p3 → p2) ∨ (p2 → (p5 ∧ p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : ((p3 → p2) ∨ (p2 → (p5 ∧ p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h8
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187066515121851420999795848835 : (((p2 ∨ p3) ∧ (((((p5 ∧ p2) ∧ p5) ∨ p4) ∧ p4) ∨ True)) → ((((True → False) → (p3 ∨ (p4 ∧ p3))) ∨ True) ∨ ((True → p5) → p5))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h9.left
        let h12 := h9.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Conjunctions on the left can always be decomposed.
        let h22 := h20.left
        let h23 := h20.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h24 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h25 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264492027441763217024954181311 : (True ∧ (((p5 ∧ False) → p3) ∧ (((p2 ∨ p3) ∧ ((p3 → p1) → (p4 ∧ False))) → (p1 → (((p3 ∨ p5) ∨ (False → p5)) ∧ (p3 → False)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h4.left
  let h14 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h15 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h16 : (p3 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h17
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h18 := h14 h16
    -- We need to get the right conjuct of h18 based on <expert-advice>.
    let h19 := h18.right
    -- False on the left can always be used.
    apply False.elim h19
  case inr h20 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h21 : (p3 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h22
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h23 := h14 h21
    -- We need to get the right conjuct of h23 based on <expert-advice>.
    let h24 := h23.right
    -- False on the left can always be used.
    apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_823789497228066983308847773264 : ((((((p5 ∧ p5) → (p1 → p1)) ∧ (((p5 → False) ∧ p5) ∧ (((True ∨ p5) ∨ p3) → (p4 → (((p4 ∧ p5) ∨ p2) ∨ p5))))) ∧ True) → p3) ∧ True) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h10 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h11 := h8 h10
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190384446653596703554120416232 : (((True ∧ (((p1 → (p2 → False)) ∨ p2) ∧ True)) ∨ False) ∨ (False ∨ (((p1 → (p4 ∨ True)) ∨ (((True → p3) ∧ p1) ∨ (p3 ∧ p2))) ∨ p1))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_222277435684136451101928547052 : (((False → p3) → True) ∧ ((((True → (p1 ∨ (p2 ∧ True))) ∧ ((p2 ∨ p2) ∨ ((p3 → False) → (False ∨ p3)))) → (False ∧ False)) ∨ (True ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137751749308089932880238179694 : ((p2 ∨ ((((p4 ∨ (p3 ∨ p5)) → (True → p2)) → (True ∧ (p3 → ((p2 ∨ ((p4 ∧ p5) → p2)) ∧ p4)))) ∨ True)) ∨ ((p2 ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57872012219459182008100534201 : (((p1 ∨ (True ∨ p4)) → ((((p1 ∨ p1) → (p1 ∨ (p5 ∧ (p5 ∧ ((p5 ∨ p4) ∧ p3))))) ∧ ((False ∨ True) → p1)) → (p2 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158957418764285899112260443156 : ((p2 ∨ (p5 ∧ ((((p2 → p4) ∨ (False → p5)) ∧ True) → ((False ∨ ((p2 ∧ True) → p5)) → False)))) ∨ (True ∨ (True → ((p5 ∨ False) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233579314599082102434674496358 : ((p1 ∨ (p3 → p5)) → ((p2 ∧ ((p2 ∨ True) → p1)) ∨ (((True ∨ True) ∨ (True ∨ (True ∨ ((p3 ∨ p3) ∨ p5)))) ∨ (p2 ∨ (False ∨ p3))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
theorem thm_5_vars_118875557255448860546335088307 : ((True → ((False ∧ p3) ∨ (p2 → (((p5 ∨ p5) → p2) ∧ ((p4 → (p4 → p3)) ∧ (p2 ∨ ((p2 → p4) → (p3 ∧ True)))))))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



