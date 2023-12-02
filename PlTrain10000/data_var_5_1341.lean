variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326217906402464731824745341329 : (p5 ∨ (p3 → (((((p3 ∧ (p4 ∨ ((p1 ∧ p1) ∨ (False ∨ ((False ∧ True) ∨ p2))))) ∨ ((p2 ∨ p2) ∨ p5)) → (p5 ∧ p3)) ∧ p4) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158218745491206235183915799138 : (((p2 ∧ (False ∨ True)) ∧ ((True ∧ p2) → (((((p4 ∧ (False ∧ p4)) → False) → p4) ∧ False) ∧ p5))) ∨ (True → (((p4 ∧ p1) → p1) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692227453373919052341218893566 : ((((((p3 → False) ∧ ((True ∧ (p3 ∧ (p4 → p4))) ∨ (True ∧ p4))) ∨ p4) ∧ (True → ((((True → p2) ∨ p4) → p1) ∧ (p3 ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344362504922633661662159503376 : (p2 → (p4 ∨ ((((((p1 ∧ (p3 → (p1 ∨ p5))) → p3) ∧ (p4 → (p2 → (p3 ∨ p2)))) ∧ (p1 ∧ p4)) ∨ p3) ∨ (True ∨ (True → p1))))) := by
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
theorem thm_5_vars_252998478439637038598070036817 : ((True ∧ p3) → ((p5 → (((p1 ∧ ((p1 ∧ p4) ∧ (((False ∧ p4) ∧ p4) ∨ (p3 ∨ ((p2 ∧ p3) ∧ p5))))) ∧ p4) ∨ (p2 ∧ p4))) ∨ p3)) := by
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
theorem thm_5_vars_41493291376180983240448890168 : ((((((True → (((False → True) → (True ∧ False)) ∨ p2)) ∨ True) → p2) → (p2 → (((p3 ∧ p2) → p1) ∨ ((p2 ∨ True) ∧ p4)))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202679453265952482169450449336 : (((p4 ∧ (False ∨ p5)) → (p5 ∧ True)) ∧ ((p5 ∨ ((p5 → (p1 → (False ∨ ((False ∧ (False ∧ p5)) ∨ p4)))) → p5)) ∨ (p5 ∨ (True ∨ False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322253891728818241114462193584 : (p5 ∨ ((((p3 ∧ ((p4 → (p4 ∧ (True → (p3 ∧ ((p1 ∨ p1) → p4))))) ∧ p4)) → ((p1 ∨ True) → (p5 → (False ∧ p1)))) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68969728401561599750879413862 : ((p4 → (p3 → (p4 ∧ (((((((p1 → ((p3 → p3) → p4)) ∨ p2) ∧ False) ∨ p2) ∨ (False → p5)) ∧ p1) → (True ∧ (p2 ∧ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14870420571972135927337236152 : ((((((p5 ∨ (p1 ∨ p5)) ∨ p4) ∧ (True ∧ False)) ∨ (((((p4 ∧ ((False ∨ p1) → p1)) ∨ p1) → p4) → p1) → p5)) ∨ (p5 ∨ True)) ∧ True) := by
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
theorem thm_5_vars_149583174108062440143486877035 : ((p3 ∧ (((p1 → (p3 ∧ ((((p1 ∧ p3) ∧ p3) → (p3 ∨ p5)) → (p4 → (p1 → p2))))) ∧ p2) ∨ p3)) ∨ ((p1 ∨ (p4 → p4)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117892915241324693533420881960 : ((p5 ∧ ((((False ∨ p4) ∧ (p2 → p2)) → ((((p3 ∨ p5) ∧ p2) → p1) ∨ (p5 ∧ (p1 ∧ (True ∨ p3))))) → (p3 → p2))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180339525067098129109369882683 : (((p2 ∨ ((p2 ∧ (p3 → (True ∧ True))) ∧ (p3 ∨ False))) ∧ (True ∧ p5)) → (((p3 ∨ p3) ∧ p5) → (((False ∧ (p4 ∧ p2)) ∨ True) ∧ p2))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h7.left
        let h18 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h19 =>
        -- False on the left can always be used.
        apply False.elim h19
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h1.left
    let h22 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h22.left
      let h25 := h22.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- Conjunctions on the left can always be decomposed.
      let h29 := h27.left
      let h30 := h27.right
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h22.left
        let h33 := h22.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h34 =>
        -- False on the left can always be used.
        apply False.elim h34
  -- Conjunctions on the left can always be decomposed.
  let h35 := h2.left
  let h36 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h35
  case inl h37 =>
    -- Conjunctions on the left can always be decomposed.
    let h38 := h1.left
    let h39 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h40 =>
      -- Conjunctions on the left can always be decomposed.
      let h41 := h39.left
      let h42 := h39.right
      -- One of the premise coincides with the conclusion.
      exact h40
    case inr h43 =>
      -- Conjunctions on the left can always be decomposed.
      let h44 := h43.left
      let h45 := h43.right
      -- Conjunctions on the left can always be decomposed.
      let h46 := h44.left
      let h47 := h44.right
      -- Disjunctions on the left can always be decomposed.
      cases h45
      case inl h48 =>
        -- Conjunctions on the left can always be decomposed.
        let h49 := h39.left
        let h50 := h39.right
        -- One of the premise coincides with the conclusion.
        exact h46
      case inr h51 =>
        -- False on the left can always be used.
        apply False.elim h51
  case inr h52 =>
    -- Conjunctions on the left can always be decomposed.
    let h53 := h1.left
    let h54 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h53
    case inl h55 =>
      -- Conjunctions on the left can always be decomposed.
      let h56 := h54.left
      let h57 := h54.right
      -- One of the premise coincides with the conclusion.
      exact h55
    case inr h58 =>
      -- Conjunctions on the left can always be decomposed.
      let h59 := h58.left
      let h60 := h58.right
      -- Conjunctions on the left can always be decomposed.
      let h61 := h59.left
      let h62 := h59.right
      -- Disjunctions on the left can always be decomposed.
      cases h60
      case inl h63 =>
        -- Conjunctions on the left can always be decomposed.
        let h64 := h54.left
        let h65 := h54.right
        -- One of the premise coincides with the conclusion.
        exact h61
      case inr h66 =>
        -- False on the left can always be used.
        apply False.elim h66



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227470836151922964951486508434 : ((True ∧ (p2 ∧ p3)) ∨ (((((p2 → (False → (p2 ∨ (((True → p1) ∧ p3) ∧ True)))) → p4) ∧ (p1 ∨ p4)) ∨ True) ∨ (p5 ∧ (p2 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149553088562855439717250995293 : ((p2 ∧ (((p4 → p3) ∧ ((True ∧ (p2 ∧ (False → False))) ∧ p2)) ∧ (p1 ∨ (p5 ∨ ((p3 ∨ p1) → p5))))) ∨ ((True ∨ True) ∨ (p3 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39410932210048176810137828093 : (((p4 ∧ (((((True ∨ True) ∨ (True ∧ p3)) ∨ p3) → ((p4 → p4) ∧ p4)) → ((True → False) ∧ ((p4 ∧ p2) ∨ (False → p4))))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635516758737258092506268812481 : (((((((((p1 → (p1 → p3)) → p2) ∨ False) ∧ (p2 → ((False ∨ p3) → (p5 → p1)))) ∨ False) ∨ ((p3 → (p4 ∧ p3)) ∨ p5)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150960454121261405887648000612 : (((p5 ∧ ((((p2 → (((True ∨ p2) ∨ True) ∨ p5)) ∧ ((p4 → False) ∨ (p2 ∧ False))) → p2) ∨ p1)) ∨ p1) → (p4 ∨ ((p2 → False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168196736419320507792434676843 : ((((True ∨ p1) ∨ p2) ∨ ((p4 ∨ ((p4 ∧ p5) → (False ∨ False))) ∨ ((p3 ∨ True) → False))) → (((p2 ∨ p1) → p5) ∨ ((p1 → True) ∨ False))) := by
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h5
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h7
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
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
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h15
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h17
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43898559738339310896317504078 : ((((p3 → (((p3 ∨ ((p4 ∨ (p4 → (True ∧ p1))) ∨ p3)) → p3) → ((p4 → (p5 ∧ (p5 ∧ p2))) ∧ p4))) ∧ (True ∨ p2)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40256894956422262721487511147 : ((((p2 ∨ (((p2 → ((p4 → ((p3 ∨ p4) ∨ False)) → (p2 ∨ ((p2 ∨ (p5 → p4)) ∨ (p2 ∨ True))))) → p3) ∧ p2)) ∧ False) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191363180825376380038633855257 : (((p5 ∨ p1) ∨ (p5 ∨ (((p3 ∧ True) ∨ p2) ∨ p4))) ∨ (((((p4 ∧ p4) → (p1 ∨ (p5 ∨ False))) ∨ (True → (p3 ∨ p1))) ∧ False) → p5)) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328522991779831779528374885188 : (True → (((p2 → (p1 ∨ ((True ∧ p1) → False))) ∧ (((p2 ∧ p4) ∨ p2) ∧ (p1 → True))) ∨ (p2 → (((False ∨ False) ∨ (True → False)) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2109052125814892434779299308 : ((((p5 ∨ (((p5 ∨ (True ∨ p2)) → (p2 ∧ p4)) → (False ∨ (p2 ∧ p5)))) → True) ∨ p2) → (p4 → (p5 → (p4 ∨ (p2 ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159307412249004622555499520349 : ((p5 → (((p2 → p5) → (p1 → (((p2 ∨ (p3 ∨ p4)) ∧ True) → ((p4 ∧ p4) ∨ False)))) ∨ p5)) ∨ (((True ∧ (p2 → p4)) ∨ p5) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322510222477887403074748892847 : (p5 ∨ ((False ∧ (((((p5 ∧ (p3 → (((p5 ∨ p2) ∨ (p3 → (p1 ∨ (p4 ∧ p1)))) ∧ p5))) ∨ p2) ∧ p5) → (p1 ∨ p1)) → p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213620258032975014144504798648 : ((((p2 ∧ p1) ∨ p5) ∨ p4) ∨ (((((p3 ∨ (p4 ∨ (p3 → (p4 ∨ False)))) ∧ False) → p3) → (((False → p3) → p2) ∨ (False → False))) ∨ p3)) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189940231091768284495262639040 : ((p3 → (p5 → ((((True ∨ True) ∨ False) ∨ p2) ∧ True))) ∧ ((((False ∨ (False ∨ (True → p2))) ∨ (p1 ∨ p4)) ∧ (p5 → p5)) ∨ (False → p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206459539201800664530894341960 : ((p4 ∨ (p2 ∧ (p5 ∧ (p1 ∨ p4)))) ∨ (((((p5 ∧ (p1 → True)) ∧ p2) ∧ (((p2 ∨ p5) ∨ (True ∧ p1)) ∨ (p5 ∧ p2))) ∧ p3) → p5)) := by
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
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124478435601615656740557403876 : (((((p5 ∨ (p2 ∨ p2)) ∨ p1) ∧ p3) ∧ ((p1 ∨ (p5 ∨ (p2 ∧ ((p1 ∨ p4) → (p4 ∨ (p4 → (True → True))))))) ∧ p2)) → (False ∨ p3)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h3.left
      let h9 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h3.left
        let h19 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h22 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h5
          case inr h23 =>
            -- Conjunctions on the left can always be decomposed.
            let h24 := h23.left
            let h25 := h23.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h5
      case inr h26 =>
        -- Conjunctions on the left can always be decomposed.
        let h27 := h3.left
        let h28 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h29 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h30 =>
          -- Disjunctions on the left can always be decomposed.
          cases h30
          case inl h31 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h5
          case inr h32 =>
            -- Conjunctions on the left can always be decomposed.
            let h33 := h32.left
            let h34 := h32.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h5
  case inr h35 =>
    -- Conjunctions on the left can always be decomposed.
    let h36 := h3.left
    let h37 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h36
    case inl h38 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h39 =>
      -- Disjunctions on the left can always be decomposed.
      cases h39
      case inl h40 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h41 =>
        -- Conjunctions on the left can always be decomposed.
        let h42 := h41.left
        let h43 := h41.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261546237724658131155610310165 : ((p5 → p3) → (p1 → ((((((p4 ∨ p3) → (((True ∧ p2) → p3) → ((p1 → p4) ∨ p2))) ∨ p2) → ((p5 ∨ p3) → p5)) ∨ p5) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757768178971747080593198529360 : (((p1 ∧ (False ∨ (False ∧ ((False ∧ p1) ∨ (p4 → (((False ∨ (False ∨ ((p4 → (p4 → (p3 → p1))) ∧ (False ∨ True)))) → p2) ∧ True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219411476844799035708949760888 : ((p3 ∨ (p3 → (p2 ∧ p4))) → ((True → False) → (p3 ∨ ((p4 → ((p4 ∧ ((p5 ∨ p5) ∧ p5)) ∧ (True ∧ p1))) → (False ∧ (False → p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46810556971541227846754017071 : ((((((p3 ∧ ((p2 → ((False ∧ p4) ∧ (p2 ∨ False))) ∨ p3)) → ((False → p4) ∧ (p4 ∨ (p4 ∧ True)))) ∨ p3) ∧ p4) ∨ (p5 ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309660421211966335509815107791 : (p2 ∨ ((p2 → (((p1 ∨ (p5 ∧ (p4 ∨ (p3 ∨ p1)))) ∨ (p5 → (True → (p4 ∨ (p1 ∧ (True → p2)))))) ∧ p1)) ∨ (True ∨ (p5 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709422303862865521637570241919 : ((((p1 ∧ (p1 ∨ ((p3 ∨ (p1 ∧ p4)) → p2))) → ((True → False) → (False ∧ (p4 ∧ (False ∧ ((p1 ∧ (p4 → (p2 ∧ True))) ∨ p3)))))) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- False on the left can always be used.
    apply False.elim h10
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h14
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h17 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h18 := h2 h17
    -- False on the left can always be used.
    apply False.elim h18
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h19 := h1.left
  let h20 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h20
  case inl h21 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h22 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h23 := h2 h22
    -- False on the left can always be used.
    apply False.elim h23
  case inr h24 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h25 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h26 := h2 h25
    -- False on the left can always be used.
    apply False.elim h26
  -- Conjunctions on the left can always be decomposed.
  let h27 := h1.left
  let h28 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h28
  case inl h29 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h30 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h31 := h2 h30
    -- False on the left can always be used.
    apply False.elim h31
  case inr h32 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h33 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h34 := h2 h33
    -- False on the left can always be used.
    apply False.elim h34
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57553335910154939764984045516 : ((((p3 ∧ p1) ∧ p2) → (True → (((p2 → True) → ((((True → p5) → ((False → False) ∧ (p4 ∨ (p5 ∨ False)))) ∧ False) ∧ p5)) ∨ True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667276873598885579425698608516 : (((((p4 → False) ∧ (((((((p3 ∧ p5) → p3) ∨ p3) ∨ p3) → (((p3 ∧ p1) → p4) ∧ p1)) ∨ p5) → p3)) ∧ (p4 → (p2 ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185529145784891388436998783227 : ((p3 ∨ (((p1 ∨ (p2 ∨ p4)) ∧ p1) ∨ ((False → False) ∨ p5))) ∨ (((((p5 → False) ∧ True) ∨ (p2 → (p2 ∨ p3))) ∧ (p5 ∨ p2)) ∨ p2)) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715636096377636252065096431505 : (((((True → (p1 → p1)) ∧ False) ∧ (((((p2 ∨ (((False → p5) ∧ False) ∨ False)) ∨ (p2 → (p4 → (p3 ∧ p5)))) ∨ p4) ∨ p3) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137207055217813643377346659992 : ((False ∧ (True → ((p3 ∨ ((p2 ∨ p5) ∧ (((True ∨ (p3 ∧ False)) ∨ p2) ∧ (p5 ∨ (p2 ∨ (p2 ∨ p2)))))) ∨ p5))) ∨ ((p2 → p2) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198089569991105482919831279293 : (((p5 ∨ p5) ∨ ((p4 ∧ (True ∨ False)) ∧ p4)) ∨ (((p3 → (p3 → (((False ∨ False) ∧ (p3 ∧ True)) → (p5 ∧ p3)))) ∧ True) ∧ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67382815703905621747292362079 : ((p1 → ((((True → p5) ∨ (p4 ∧ p4)) ∧ ((p2 → p4) → (p2 → (p2 ∨ ((p4 → (p5 ∨ p4)) ∧ (False ∧ (p3 ∧ p1))))))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358033031539993859295147264891 : (p5 → (p1 ∨ ((((((p5 → ((p3 ∧ ((True ∧ p1) ∨ p4)) → (True ∨ (p4 → p2)))) ∧ p2) ∨ ((False ∧ False) ∨ p1)) ∧ p3) ∨ True) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41380554448782740554852818266 : ((((((((True → p5) ∨ ((p2 ∧ p5) ∧ True)) ∧ p5) → (p5 ∧ p3)) ∧ p3) ∧ (((((p4 ∧ p3) ∧ True) → p1) ∧ p3) ∨ p2)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321675123074048659954945589306 : (p4 ∨ (p4 → (((p1 ∨ True) → (p4 ∧ ((p5 → p3) → (p2 ∨ ((((False → p1) → False) ∧ p1) → p2))))) ∨ ((p3 ∧ (p4 → p1)) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : (False → p1) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h12 := h8 h10
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h17 : (False → p1) := by
      -- Implications on the right can always be decomposed.
      intro h18
      -- False on the left can always be used.
      apply False.elim h18
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h19 := h15 h17
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49171170313056575633128776883 : (((((False → p4) ∨ (p2 ∧ (p5 → p5))) → (((p3 → ((p5 ∨ False) ∨ p3)) → True) ∧ ((p2 ∨ p4) ∧ p5))) ∨ (True → (True ∨ p3))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350299983328525895237154508995 : (p4 → ((p2 ∨ ((p5 ∨ (p1 ∨ (((((p1 → (False → (True ∨ (False ∨ p5)))) ∧ True) ∧ True) → p1) ∧ False))) ∧ (p3 → (False ∧ p4)))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310984271759230434484750098139 : (p2 ∨ ((False → p4) ∧ ((False ∧ (True → ((p1 → (True ∨ ((False ∨ ((p5 ∧ p4) ∧ p4)) → p4))) → False))) ∨ ((False ∨ (p2 → p3)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258787874209499460994031839174 : ((True → False) → (((((p1 ∧ p3) ∨ ((p4 ∧ p3) ∨ True)) ∧ p1) ∨ False) → ((p1 → p5) ∧ (p2 ∨ (p4 ∨ (p4 ∧ (p3 ∧ (False → p2)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
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
      let h8 := h7.left
      let h9 := h7.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h11 := h1 h10
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h17 := h1 h16
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h19 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h20 := h1 h19
        -- False on the left can always be used.
        apply False.elim h20
  case inr h21 =>
    -- False on the left can always be used.
    apply False.elim h21
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h28 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h29 := h1 h28
      -- False on the left can always be used.
      apply False.elim h29
    case inr h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h31.left
        let h33 := h31.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h32
      case inr h34 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h35 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h36 := h1 h35
        -- False on the left can always be used.
        apply False.elim h36
  case inr h37 =>
    -- False on the left can always be used.
    apply False.elim h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613638069309850025198477691545 : ((((((False ∨ (((p3 ∨ p2) → p4) → (((p4 ∨ p5) ∧ p4) ∧ (p2 ∧ p2)))) ∧ ((p4 → False) ∧ p1)) ∧ (p2 → (p4 ∨ p1))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71383864878046111377829534845 : ((((p1 → True) ∧ ((((False ∧ p3) ∨ ((p1 ∨ (p3 ∧ p2)) → p2)) ∨ ((((p5 ∧ True) → p4) ∨ (p1 ∨ p3)) ∨ p4)) → False)) ∧ p3) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((False ∧ p3) ∨ ((p1 ∨ (p3 ∧ p2)) → p2)) ∨ ((((p5 ∧ True) → p4) ∨ (p1 ∨ p3)) ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254003199465301801577417325084 : ((p1 ∧ p5) → (True ∧ ((((p2 → p3) → (False ∧ (((p1 → True) → p5) → p3))) ∨ True) ∨ (((True → p1) → p3) → ((False → p2) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_116583991787123440885229208348 : (((p4 ∨ False) ∧ (p1 ∧ (False ∨ (((False ∧ (p2 ∧ (((p5 ∨ (p2 ∧ (False → p5))) ∨ p2) ∧ (p4 → p5)))) → p1) → p1)))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317021137269730264213574057718 : (p3 ∨ (p3 → (True → (((((p3 ∨ p1) → (p3 → ((True → True) ∧ False))) ∨ (((p2 ∨ (True → p2)) ∧ p4) ∧ p1)) ∨ (p3 ∨ p5)) ∧ True)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746350066601465559916891764290 : ((((p2 ∨ False) → ((True ∧ (((p5 → p4) ∧ p1) ∧ ((p3 → (False ∧ False)) ∨ (p2 ∨ p5)))) → ((p4 ∨ (False ∨ (p3 ∧ p1))) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330887187719483205268340812755 : (True → (p3 → (p2 ∨ ((p2 → ((((p1 ∨ p3) ∧ (p5 → ((p1 → p1) ∧ ((False ∧ p1) ∨ ((p1 ∨ p5) → p5))))) → p2) → p1)) ∨ True)))) := by
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
theorem thm_5_vars_669670468652679870749765368312 : ((((((p5 ∧ ((False ∧ p2) ∨ (((False ∧ p2) → (True ∧ p1)) ∨ p3))) ∨ (True → True)) → ((p2 → p2) ∧ p2)) ∨ ((p1 ∧ False) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_452339104896902057981807676701 : ((((p1 ∧ (p2 ∨ (((p3 ∨ (((p5 ∧ False) → (p4 → (p3 ∨ (p4 ∧ p4)))) ∨ True)) ∨ p3) ∧ p4))) ∨ (p5 ∨ (p1 → (False ∨ p1)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144774165802423622299050694346 : ((((p4 ∧ ((p3 ∧ p3) ∧ p2)) ∨ ((p1 → ((p4 ∨ True) ∨ (False ∧ p1))) ∧ p3)) ∨ (p2 ∨ (p2 → p2))) ∧ (True ∨ (False → (False → False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764277018970268684900364965809 : (((p4 ∧ (((True → (((p2 ∨ True) → (((False ∨ p4) ∨ (((p3 ∧ p1) ∧ False) → p2)) ∧ (p5 → p2))) ∨ (p4 ∨ p1))) → False) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134097284519841407301585961793 : ((((p2 ∨ ((((False → p2) ∧ (((p3 → p1) → ((p2 → p5) ∨ p2)) → p2)) ∧ (p5 → p5)) → p4)) → False) ∨ p5) ∨ ((p5 ∨ p5) → p5)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53101026265804133376157010424 : (((p5 ∨ (((p3 ∨ p1) ∨ ((p3 → True) ∨ (p5 → True))) → False)) ∧ (p5 ∧ ((((p4 ∧ (p3 ∨ p1)) ∨ (p3 → True)) ∨ p5) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299260714647951055074355027272 : (False ∨ (((((((p5 ∨ (((p5 ∧ (p4 ∨ p2)) ∧ p5) → (p2 ∨ True))) ∧ True) ∨ p5) ∧ p4) → True) → (((p5 ∧ p4) → False) ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143076278336789208301261128726 : ((False → ((True ∧ False) ∨ ((p2 ∨ ((p5 ∨ p4) → p2)) → ((((p4 ∨ p5) ∧ p4) → ((True ∨ p2) → p3)) → p2)))) → ((True → p2) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164635268680598774961385772502 : (((p2 ∨ (p5 ∧ (((p2 ∧ (p3 → ((p3 ∧ p4) ∨ (p2 ∧ False)))) ∨ True) ∧ p5))) ∧ p5) ∨ (p5 ∨ ((True ∨ (p3 ∨ (p2 → True))) ∨ p2))) := by
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
theorem thm_5_vars_179162035668084350152268710227 : ((p2 ∧ (((p5 ∧ p3) ∨ p2) ∨ (((p4 ∧ p5) → p3) ∨ (p3 → True)))) ∨ (False → (p5 ∨ (((p3 ∧ True) ∨ p1) ∧ (True ∨ (p3 ∧ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597368439827107032516797147958 : (((((((True ∨ True) → p4) ∧ p5) ∨ (((p1 ∧ p2) ∨ (p5 ∨ (False ∨ (p3 ∧ (False ∨ (p4 ∧ (p1 ∨ True))))))) ∨ (p4 ∨ p2))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137730665999892510109313781689 : ((p1 ∨ (False ∨ ((((((p2 ∨ (p1 ∧ True)) → (((p5 ∨ p5) ∧ p5) ∨ False)) ∨ (p3 → True)) ∨ p3) ∧ p2) ∨ True))) ∨ (p1 → (p3 ∧ p5))) := by
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
theorem thm_5_vars_350031619435636860557633123107 : (p4 → ((((p5 → ((p1 ∨ (((p5 → p5) ∨ True) → p1)) ∧ (p1 ∨ (p3 → p2)))) → (p2 ∧ (((False ∨ p4) ∨ p4) → p1))) → p1) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256440609309434170519226109294 : ((False ∨ p3) → (p2 ∨ ((p4 ∨ p2) → ((p3 → (((p1 → (True → p3)) → (p4 ∧ p4)) ∧ (False ∨ False))) ∨ ((p1 ∧ p2) → (True ∧ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773439451588828623068933124921 : (((False ∨ ((((((True → p3) ∧ (((p5 → (((p3 ∨ False) ∨ p1) ∨ p5)) → p4) → (p4 → p4))) ∨ p3) → (True → p3)) ∨ False) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_319686328243135012155612610050 : (p4 ∨ ((p3 ∨ (p3 → ((p3 ∨ p1) ∨ (p2 → p2)))) → (False ∨ (((((p4 ∧ p3) ∨ p2) → p3) → p5) ∨ (p3 → ((True → p2) ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738343972415758742720714529166 : ((((p1 ∧ False) ∨ (((p2 → False) ∨ (True → (((p1 ∨ ((p2 → (False ∧ (p1 → p2))) → (p5 → False))) ∧ False) ∨ (False → p3)))) ∧ True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326283970991098069411359536245 : (p5 ∨ (p4 → ((p4 → ((False ∨ ((True → p2) → p2)) → (((p2 ∨ ((True ∨ ((p4 ∧ (p2 ∧ False)) → p3)) → p2)) ∨ True) ∧ p4))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136335384047630666332858811219 : (((False ∧ ((p2 ∧ p5) ∧ p3)) ∧ (((((((p5 ∨ True) → (p2 ∨ True)) → (p5 ∧ p2)) ∨ p5) → p1) ∧ p3) ∨ p3)) ∨ ((False ∧ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44139068708744670978237074623 : ((((True → (p5 ∨ (((p4 ∧ p4) ∨ True) ∨ ((False → False) → (p5 ∧ (p3 → (p5 → (p4 ∨ p3)))))))) ∨ ((p4 ∧ p1) → p2)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195178526199096359915938497303 : ((((p4 ∨ (p5 ∨ p2)) ∧ p3) ∨ (False ∨ True)) ∧ (((True ∨ ((False ∨ ((p3 ∨ (True ∨ True)) → p4)) ∧ p2)) ∧ ((False → False) ∧ p3)) → True)) := by
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
theorem thm_5_vars_158418786394509582768705196185 : (((p3 ∧ p3) ∨ (((True → (p5 ∨ p3)) → (p5 ∨ (((p4 ∧ p4) → (p1 ∧ p3)) ∧ p5))) ∧ p5)) ∨ ((p2 → (True ∨ p1)) ∧ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321311454801263310046511500951 : (p4 ∨ (p5 ∨ ((True ∨ (((p5 → ((p3 ∨ False) ∨ ((p3 ∨ True) → (False ∧ p4)))) ∨ p4) ∧ (p1 ∧ p5))) → (False ∨ (p2 ∨ (True ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h5.left
      let h11 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117965445763967388569265181003 : ((p5 ∧ (p3 → ((True ∧ (p3 ∧ (((True ∨ (((p2 ∧ (p3 ∨ p3)) ∨ (p5 ∨ p5)) ∧ (p1 → p2))) ∧ False) ∨ p5))) ∨ p2))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585562202601405287997576268585 : (((((((((p5 → p2) ∧ p3) ∨ (p4 ∨ p2)) ∨ (True → (((p3 → (p4 → p2)) ∧ (p2 ∧ (p2 → p1))) ∧ p1))) ∨ p3) ∧ p4) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208007131575997597141337451594 : ((((p1 ∧ p4) → True) ∨ (p2 ∨ p3)) → ((((p2 ∧ False) ∧ ((False ∨ ((p3 ∨ (p4 ∨ p5)) → p2)) ∧ (False ∧ (False ∨ p2)))) ∨ True) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48543855937514857649562230013 : (((((p4 ∨ ((((True → p5) ∨ (p4 ∧ (p4 ∧ False))) → p4) ∧ (False → ((p1 ∧ False) → p3)))) ∧ p4) → p5) ∧ ((p2 → True) → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55670452878732547117493567532 : ((((p2 → (p4 ∨ p3)) ∧ p5) ∧ (p2 ∧ (p4 → (((p1 ∧ (((p5 ∧ p2) → p3) → p2)) ∨ (True ∧ False)) ∧ ((p2 ∨ p1) → p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173475673556221522711265358241 : ((((p3 → (((((p5 ∧ p3) ∧ (p5 → p1)) ∨ p3) ∧ p1) ∨ p3)) ∨ p3) ∧ p1) → ((p3 → p4) → (((p1 ∨ False) → False) → (p2 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : (p1 ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : (p1 ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653795814543129506580628447319 : ((((((p5 → (p3 → (((p5 → (((False ∧ False) ∨ True) ∧ p2)) ∨ False) ∧ p5))) ∨ ((p5 → p4) ∧ (p5 → p2))) ∧ p5) ∨ (p1 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136378217332568568140380344575 : ((((p2 ∧ p3) ∧ (p2 ∧ p4)) ∨ ((((p4 ∨ (True → ((p4 → p1) ∨ (p4 ∨ p1)))) ∨ p4) ∧ p5) ∨ (p4 → True))) ∨ ((False → p4) ∨ p1)) := by
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
theorem thm_5_vars_328907332243827004585584017854 : (True → (((p5 ∧ ((p4 ∨ (False ∨ False)) → False)) ∧ p5) → (((p4 → p1) ∧ p1) → ((((p2 ∧ p5) → ((p5 ∧ p2) ∧ False)) ∨ p4) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214927231362769125133509970765 : (((True ∧ p4) → (False ∧ p5)) ∨ (((False ∧ (((p5 → p5) ∧ (p3 ∧ (p4 ∨ ((False ∧ True) ∧ (p4 ∧ p2))))) ∧ True)) ∧ (False ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196712409898755497090664587043 : ((((((p2 ∨ p2) ∨ p4) ∨ p3) → False) ∧ p5) ∨ (((p2 → ((p5 ∧ (p4 ∧ p5)) ∨ (p4 → p5))) ∧ p5) ∨ (p4 → ((p2 → p2) ∧ True)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178587355133515828428520352837 : (((((p3 ∨ p2) ∧ (p4 ∨ p2)) ∨ p1) ∨ (p5 → (False ∧ (p5 ∨ True)))) ∨ (True → ((p3 ∧ False) → ((p1 ∨ (True → (p5 → p1))) ∨ p5)))) := by
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
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119110660327363530495240744054 : ((p1 → ((False → p2) ∧ (((p3 ∨ False) ∨ (p3 → False)) ∧ (((p3 ∨ p3) → (((p5 ∧ False) ∧ p2) ∧ (p2 → False))) ∧ p5)))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683792432182825774189557197189 : ((((((p4 ∧ ((((p4 ∨ (p3 ∧ p3)) ∧ p1) ∧ (p3 ∨ p5)) ∧ True)) ∨ (True ∧ True)) ∨ p1) ∨ ((((p4 ∨ True) → p2) → p4) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_41538561611645898362346390342 : (((((False ∨ (((p4 ∨ p4) ∧ p4) ∨ p4)) ∨ (True ∨ p5)) ∨ (p2 → (((p1 → (((p3 ∧ p3) ∨ p4) ∨ p2)) ∨ p4) → p3))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161329938155626993895527476689 : ((True ∧ (p3 ∧ (p3 ∧ ((True → ((p4 ∧ p4) ∧ ((p5 ∨ True) ∧ False))) ∧ (p2 → (p5 ∨ p5)))))) → ((False → False) → ((True ∧ False) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h12 := h9 h11
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- False on the left can always be used.
  apply False.elim h14
  -- Conjunctions on the left can always be decomposed.
  let h15 := h1.left
  let h16 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h17 := h16.left
  let h18 := h16.right
  -- Conjunctions on the left can always be decomposed.
  let h19 := h18.left
  let h20 := h18.right
  -- Conjunctions on the left can always be decomposed.
  let h21 := h20.left
  let h22 := h20.right
  -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
  have h23 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h21, we can now drive its conclusion.
  let h24 := h21 h23
  -- We need to get the right conjuct of h24 based on <expert-advice>.
  let h25 := h24.right
  -- We need to get the right conjuct of h25 based on <expert-advice>.
  let h26 := h25.right
  -- False on the left can always be used.
  apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25588862304543507451200144615 : (((p1 → (p1 ∨ p4)) → ((((p1 ∧ (((p1 → p1) ∧ (p5 → ((p5 ∧ True) ∨ p2))) → ((p4 ∨ p3) → p5))) → False) ∨ p2) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207825347639244771712215817820 : (((p5 → ((p5 ∨ p1) ∨ p2)) → p1) → (p1 ∧ ((p1 ∨ False) ∨ ((p3 → (p2 → (((True ∧ p2) → (False ∨ p4)) → (True ∨ False)))) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → ((p5 ∨ p1) ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p5 → ((p5 ∨ p1) ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190579525160923075272991270414 : (((((p3 → True) ∨ p4) → ((p1 ∧ True) ∨ p1)) → False) ∨ ((((p5 ∧ (((p1 ∧ (True ∨ p2)) ∧ p5) ∨ (p3 ∧ False))) → p1) → False) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∧ (((p1 ∧ (True ∨ p2)) ∧ p5) ∨ (p3 ∧ False))) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- False on the left can always be used.
      apply False.elim h15
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h2
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136812576055460278218809882825 : (((p4 → p5) ∧ (((p4 ∨ (True → (False ∨ p4))) → False) ∧ ((p2 ∧ (p2 → p1)) ∧ (True → (p1 ∧ (p5 → p3)))))) ∨ (True ∨ (p1 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



