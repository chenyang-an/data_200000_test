variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134595497327356888862457632053 : (((((((p3 → (((p5 ∨ p3) ∨ p1) → ((p3 → p5) → p5))) → p3) ∨ False) ∨ (p3 → p5)) → (p3 ∧ False)) → False) ∨ ((p5 → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303441593675980738033459582969 : (p1 ∨ (((False ∨ (((p5 ∧ ((p4 ∨ ((False ∨ (True ∧ p3)) ∧ p3)) ∨ p1)) ∧ False) ∨ ((False ∨ p3) → p4))) ∨ ((False → p3) ∨ p1)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45992095253832775642315798224 : (((((((True ∧ p2) ∨ p3) ∨ (((((p5 ∧ p5) → (False ∨ p2)) ∧ (p3 ∧ p2)) ∧ p2) → (p3 ∧ p4))) → p1) ∧ p4) ∧ (p2 → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254776399949547070454233437425 : ((p3 ∧ p4) → (((p5 ∧ (True ∨ (p3 → p4))) ∨ (p4 ∧ ((False ∧ p1) ∨ (False ∨ p3)))) ∧ (False ∨ (p5 → (((p5 → p2) ∨ p2) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109650189782424398262399322111 : ((p4 ∨ (((p2 ∧ (True ∧ ((p1 ∧ p1) ∨ p1))) → (p3 ∨ (p5 ∧ (p5 → ((p5 ∧ (False ∧ p2)) ∨ (p3 ∧ p1)))))) ∨ True)) ∧ (True ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57256929314318118414604323755 : ((((True ∨ p3) → p4) ∨ ((p4 ∧ (p4 → (((p3 ∧ p3) ∨ (p1 → p3)) ∧ p1))) → (((True ∧ p5) → ((True ∨ p5) ∧ False)) ∨ p4))) ∨ p5) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313994434494169968468039172174 : (p3 ∨ (((False ∧ p1) ∧ (((((p4 ∨ (p2 ∧ p1)) → p4) ∧ (False ∧ p1)) ∨ (p5 → p3)) ∨ ((p2 ∧ p1) ∨ (p3 ∨ p1)))) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685652545763576402820449103253 : (((((((p3 → ((p3 ∧ True) ∨ p1)) ∧ False) → (((p4 ∧ (p4 → p1)) ∨ False) ∨ p4)) ∨ p5) → (True → ((p3 → (p5 → True)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121841151164894101568943670302 : ((((p4 ∨ p4) ∨ ((p2 ∧ p5) ∨ ((p3 ∧ p4) → ((False → (p2 ∧ ((p3 → (p4 ∨ False)) ∧ False))) ∧ (p4 ∨ p4))))) → False) → (True → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p4 ∨ p4) ∨ ((p2 ∧ p5) ∨ ((p3 ∧ p4) → ((False → (p2 ∧ ((p3 → (p4 ∨ False)) ∧ False))) ∧ (p4 ∨ p4))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h5
    -- False on the left can always be used.
    apply False.elim h5
    -- Conjunctions on the left can always be decomposed.
    let h7 := h4.left
    let h8 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h3
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172295915315483931590684845301 : ((((False → (((p5 → True) → p4) ∨ p3)) ∨ p4) → (p4 ∨ (p1 ∨ (p3 ∧ p5)))) ∨ (((p2 → (p2 ∨ False)) ∨ ((p5 ∧ p2) → p2)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353578440526970782146869659067 : (p4 → (p3 ∨ (p3 ∨ ((p5 ∧ ((p2 ∨ p4) ∧ p5)) ∨ (((p4 → False) ∨ (p4 ∧ ((p1 → True) ∨ (p4 ∧ p5)))) ∧ ((True ∨ p3) ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260365490170019742591552886233 : ((p2 → p5) → ((p2 → ((p1 ∨ (p5 → p3)) ∨ ((p5 ∨ (p1 ∧ p2)) ∧ p4))) ∨ (p2 ∨ ((True ∧ (p3 ∨ True)) ∨ (p2 → (p2 ∧ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729218738326177277210761235619 : (((((p4 → False) ∧ p2) → ((False ∨ ((False → p5) → p4)) → (((p3 → False) ∨ (((True → (p1 → p1)) ∨ p4) ∨ p3)) → (False ∧ p5)))) ∨ False) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h1.left
      let h8 := h1.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h9 : (False → p5) := by
        -- Implications on the right can always be decomposed.
        intro h10
        -- False on the left can always be used.
        apply False.elim h10
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h11 := h6 h9
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h12 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h13 := h7 h12
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h17 =>
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h1.left
          let h20 := h1.right
          -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
          have h21 : (False → p5) := by
            -- Implications on the right can always be decomposed.
            intro h22
            -- False on the left can always be used.
            apply False.elim h22
          -- We have shown the premise of h18, we can now drive its conclusion.
          let h23 := h18 h21
          -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
          have h24 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h23
          -- We have shown the premise of h19, we can now drive its conclusion.
          let h25 := h19 h24
          -- False on the left can always be used.
          apply False.elim h25
      case inr h26 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h27 =>
          -- False on the left can always be used.
          apply False.elim h27
        case inr h28 =>
          -- Conjunctions on the left can always be decomposed.
          let h29 := h1.left
          let h30 := h1.right
          -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
          have h31 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h26
          -- We have shown the premise of h29, we can now drive its conclusion.
          let h32 := h29 h31
          -- False on the left can always be used.
          apply False.elim h32
    case inr h33 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h34 =>
        -- False on the left can always be used.
        apply False.elim h34
      case inr h35 =>
        -- Conjunctions on the left can always be decomposed.
        let h36 := h1.left
        let h37 := h1.right
        -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
        have h38 : (False → p5) := by
          -- Implications on the right can always be decomposed.
          intro h39
          -- False on the left can always be used.
          apply False.elim h39
        -- We have shown the premise of h35, we can now drive its conclusion.
        let h40 := h35 h38
        -- We want to use the implication h36 based on <expert-advice>. So we show its premise.
        have h41 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h40
        -- We have shown the premise of h36, we can now drive its conclusion.
        let h42 := h36 h41
        -- False on the left can always be used.
        apply False.elim h42
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h43 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h44 =>
      -- False on the left can always be used.
      apply False.elim h44
    case inr h45 =>
      -- Conjunctions on the left can always be decomposed.
      let h46 := h1.left
      let h47 := h1.right
      -- We want to use the implication h45 based on <expert-advice>. So we show its premise.
      have h48 : (False → p5) := by
        -- Implications on the right can always be decomposed.
        intro h49
        -- False on the left can always be used.
        apply False.elim h49
      -- We have shown the premise of h45, we can now drive its conclusion.
      let h50 := h45 h48
      -- We want to use the implication h46 based on <expert-advice>. So we show its premise.
      have h51 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h50
      -- We have shown the premise of h46, we can now drive its conclusion.
      let h52 := h46 h51
      -- False on the left can always be used.
      apply False.elim h52
  case inr h53 =>
    -- Disjunctions on the left can always be decomposed.
    cases h53
    case inl h54 =>
      -- Disjunctions on the left can always be decomposed.
      cases h54
      case inl h55 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h56 =>
          -- False on the left can always be used.
          apply False.elim h56
        case inr h57 =>
          -- Conjunctions on the left can always be decomposed.
          let h58 := h1.left
          let h59 := h1.right
          -- We want to use the implication h57 based on <expert-advice>. So we show its premise.
          have h60 : (False → p5) := by
            -- Implications on the right can always be decomposed.
            intro h61
            -- False on the left can always be used.
            apply False.elim h61
          -- We have shown the premise of h57, we can now drive its conclusion.
          let h62 := h57 h60
          -- We want to use the implication h58 based on <expert-advice>. So we show its premise.
          have h63 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h62
          -- We have shown the premise of h58, we can now drive its conclusion.
          let h64 := h58 h63
          -- False on the left can always be used.
          apply False.elim h64
      case inr h65 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h66 =>
          -- False on the left can always be used.
          apply False.elim h66
        case inr h67 =>
          -- Conjunctions on the left can always be decomposed.
          let h68 := h1.left
          let h69 := h1.right
          -- We want to use the implication h68 based on <expert-advice>. So we show its premise.
          have h70 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h65
          -- We have shown the premise of h68, we can now drive its conclusion.
          let h71 := h68 h70
          -- False on the left can always be used.
          apply False.elim h71
    case inr h72 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h73 =>
        -- False on the left can always be used.
        apply False.elim h73
      case inr h74 =>
        -- Conjunctions on the left can always be decomposed.
        let h75 := h1.left
        let h76 := h1.right
        -- We want to use the implication h74 based on <expert-advice>. So we show its premise.
        have h77 : (False → p5) := by
          -- Implications on the right can always be decomposed.
          intro h78
          -- False on the left can always be used.
          apply False.elim h78
        -- We have shown the premise of h74, we can now drive its conclusion.
        let h79 := h74 h77
        -- We want to use the implication h75 based on <expert-advice>. So we show its premise.
        have h80 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h79
        -- We have shown the premise of h75, we can now drive its conclusion.
        let h81 := h75 h80
        -- False on the left can always be used.
        apply False.elim h81
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45578808121879013864000429703 : (((p2 ∨ (p4 → ((p3 ∨ (((True ∧ p5) ∧ p5) → True)) → (False ∧ (p3 ∧ (False ∨ ((p2 → (p2 ∨ p4)) → (p4 ∧ p3)))))))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232483252845970953197415153970 : ((True ∧ (p5 ∨ True)) → (((((p5 → (p5 ∧ p2)) ∧ (p2 ∨ ((p4 ∨ False) → False))) → p1) → (p2 ∨ ((p2 → (False ∨ False)) ∨ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38157891748115909401561997291 : ((((((True ∧ ((((p4 ∧ p1) → p5) ∧ p1) ∨ False)) ∨ (p1 ∧ (p4 → ((False → False) ∨ True)))) → False) ∨ (p5 ∨ (p1 → True))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301154169978100674744463376023 : (False ∨ (((p4 → p5) ∨ (p2 → (p3 ∧ (True ∨ p2)))) ∨ ((p2 ∧ (p5 ∧ (p1 → (p3 → ((((p5 ∨ p4) → p2) ∧ p5) ∧ True))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53329227402618854755640780192 : (((((((((p1 ∨ False) ∨ False) ∨ p1) ∧ p5) ∨ True) ∧ True) ∧ p5) → (p1 → (((False ∨ p1) ∧ p5) ∧ (((p3 → p2) ∧ p4) ∨ p5)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h13 =>
          -- False on the left can always be used.
          apply False.elim h13
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Conjunctions on the left can always be decomposed.
  let h17 := h1.left
  let h18 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h19 := h17.left
  let h20 := h17.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h27 =>
          -- False on the left can always be used.
          apply False.elim h27
      case inr h28 =>
        -- False on the left can always be used.
        apply False.elim h28
    case inr h29 =>
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h30 =>
    -- One of the premise coincides with the conclusion.
    exact h18
  -- Conjunctions on the left can always be decomposed.
  let h31 := h1.left
  let h32 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h33 := h31.left
  let h34 := h31.right
  -- Disjunctions on the left can always be decomposed.
  cases h33
  case inl h35 =>
    -- Conjunctions on the left can always be decomposed.
    let h36 := h35.left
    let h37 := h35.right
    -- Disjunctions on the left can always be decomposed.
    cases h36
    case inl h38 =>
      -- Disjunctions on the left can always be decomposed.
      cases h38
      case inl h39 =>
        -- Disjunctions on the left can always be decomposed.
        cases h39
        case inl h40 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h32
        case inr h41 =>
          -- False on the left can always be used.
          apply False.elim h41
      case inr h42 =>
        -- False on the left can always be used.
        apply False.elim h42
    case inr h43 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h32
  case inr h44 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173288916047109412797425714273 : ((p1 → ((((p5 ∨ (p5 ∧ p4)) ∨ (p2 ∧ p2)) → ((p2 ∧ p3) ∨ p3)) ∨ True)) ∨ ((False ∧ ((False → p1) ∨ (True → p4))) ∨ (p4 → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118339417029904080093935193239 : ((p2 ∨ ((((p1 → ((True → p2) → (((p1 ∧ (p3 ∧ p1)) ∨ (p5 ∧ p5)) ∨ p3))) → p1) ∨ (p2 → (True ∨ p1))) ∨ True)) ∨ (p5 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606372578530085653710704852558 : (((((((True ∧ ((False ∧ (p2 ∧ p3)) ∧ (p3 ∨ ((p3 → p2) ∧ (True ∨ p4))))) ∨ (p5 ∨ ((p1 ∧ False) ∧ p2))) ∨ p4) ∧ p4) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259067025212858801416685034280 : ((True → p5) → ((((((False ∨ (((((True → (True → p4)) ∧ p2) → p5) → (True ∨ p3)) ∨ (False ∧ p3))) → p1) ∧ p3) → p4) → p5) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42155723793925438455374131462 : ((((p1 → p5) → ((((p2 → False) ∧ (p1 ∨ ((((True → (p5 ∨ p5)) ∨ p5) ∧ p2) ∧ ((False ∧ p4) ∨ p4)))) → p1) → p5)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183775304812765742386499021525 : (((((((False → p4) ∧ p3) ∧ p5) ∧ (p3 ∧ p4)) ∧ p5) ∧ p3) ∨ ((p3 → p4) → ((p2 ∨ ((True ∧ p2) ∧ p4)) ∨ ((False ∧ True) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175046833012045614487691860282 : ((p2 ∧ ((((p5 ∨ (p2 → True)) ∨ (p4 → (True → p2))) ∨ True) ∨ (p3 → True))) → (p5 → ((((True ∨ False) ∨ p5) → (p3 ∧ False)) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h10 : ((True ∨ False) ∨ p5) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h9
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h11 := h3 h10
          -- We need to get the right conjuct of h11 based on <expert-advice>.
          let h12 := h11.right
          -- False on the left can always be used.
          apply False.elim h12
        case inr h13 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h14 : ((True ∨ False) ∨ p5) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h15 := h3 h14
          -- We need to get the right conjuct of h15 based on <expert-advice>.
          let h16 := h15.right
          -- False on the left can always be used.
          apply False.elim h16
      case inr h17 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h18 : ((True ∨ False) ∨ p5) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h19 := h3 h18
        -- We need to get the right conjuct of h19 based on <expert-advice>.
        let h20 := h19.right
        -- False on the left can always be used.
        apply False.elim h20
    case inr h21 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h22 : ((True ∨ False) ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h23 := h3 h22
      -- We need to get the right conjuct of h23 based on <expert-advice>.
      let h24 := h23.right
      -- False on the left can always be used.
      apply False.elim h24
  case inr h25 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h26 : ((True ∨ False) ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h27 := h3 h26
    -- We need to get the right conjuct of h27 based on <expert-advice>.
    let h28 := h27.right
    -- False on the left can always be used.
    apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40353946404947373636856502954 : (((((((p5 → ((True → ((p5 ∨ (p5 ∧ ((p2 ∨ (False → True)) ∨ p2))) ∧ p1)) ∨ (p5 ∧ p1))) ∨ p2) → True) → False) ∨ True) ∨ p1) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714302813584930247567771130907 : ((((((p2 ∧ p1) ∨ p4) ∨ (p1 ∧ p5)) → (((p5 → (p4 → ((p5 ∨ True) → p2))) ∧ (p1 ∧ (p3 → p2))) → ((p4 → False) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215583822787322235154632592743 : ((p5 ∧ (p1 ∧ (p1 ∧ p1))) ∨ ((False ∨ (((p4 → True) ∨ p1) ∧ ((p2 ∨ False) ∨ p1))) ∨ (p1 → (True → ((p4 ∨ (p5 ∨ p3)) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135884024055718429276175979583 : (((False ∨ (((p2 ∨ (p3 ∧ False)) → ((p1 ∧ p1) ∧ p5)) → p4)) ∨ (((p3 ∨ p3) ∧ True) → (True ∨ (p5 ∧ p4)))) ∨ ((p2 ∧ p4) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116638226139343931187891525149 : (((p2 → False) ∧ ((((((False ∨ p3) → ((False ∨ (p2 ∧ p5)) → p3)) ∨ p5) → (((p5 ∧ p3) → True) ∧ True)) ∨ p1) → p4)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68967273802318724397824982177 : ((p4 → (p3 → ((p2 ∨ ((True → p5) ∧ (((p4 ∨ (p1 ∨ (p3 → (True → True)))) ∨ p1) ∧ (p4 ∨ (p1 ∧ p4))))) → (p1 ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709719573050056988175826727847 : ((((True → ((p5 ∨ True) ∨ (False ∧ (p5 ∧ p3)))) → (True → ((((((p2 ∧ True) ∧ (p1 → p2)) → p5) ∧ True) → p1) ∧ (False ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119460116094241565947486675612 : ((p4 → ((p2 ∧ (p5 → p4)) ∨ ((p2 ∧ (False → True)) ∨ ((p5 ∨ ((False ∧ ((p5 ∧ p2) ∧ (p2 → p3))) ∧ p2)) ∧ p3)))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250973245611040283089276583736 : ((p1 → p4) ∨ (False ∨ (((p3 → p3) → True) ∧ (p5 → (((((True ∨ p1) ∨ p4) → p4) ∨ False) → ((True → ((p1 → p4) → p1)) ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157353938178082677186272549635 : (((True → (p4 ∧ (((p5 → ((p4 ∧ (True → (p4 → p4))) ∨ (p3 ∧ p4))) → p3) ∨ True))) → p5) ∨ ((p2 ∧ (False → (p4 ∨ True))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300662079965900727582143815578 : (False ∨ (((((p3 ∧ p3) ∧ ((False ∧ p1) ∧ (p1 ∧ ((True ∧ (False ∧ False)) → False)))) ∨ True) ∧ False) ∨ (False ∨ (p1 → ((p1 ∨ p1) ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174143561043899142582919590796 : ((((((p3 → p2) ∨ (False ∧ p3)) ∨ ((False ∨ True) ∨ p2)) → p5) ∨ (p3 ∨ p5)) → ((p3 ∨ (p4 ∨ (p1 ∨ ((p2 ∨ p1) → True)))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54722263893365276815253130789 : (((((True ∧ p1) ∨ p5) ∧ (p4 ∨ (True → p4))) → (((((p4 ∨ (p2 ∧ False)) → True) → False) ∨ (((p3 → True) ∨ p3) ∨ False)) ∧ p4)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    cases h3
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h15
      -- True on the right can always be proven directly.
      apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h21 =>
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h22 =>
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h23 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h24 := h22 h23
      -- One of the premise coincides with the conclusion.
      exact h24
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h26 =>
      -- One of the premise coincides with the conclusion.
      exact h26
    case inr h27 =>
      -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
      have h28 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h27, we can now drive its conclusion.
      let h29 := h27 h28
      -- One of the premise coincides with the conclusion.
      exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300679951458742335105196481575 : (False ∨ (((((p2 → p3) → (p4 ∧ False)) → (p4 ∧ p1)) → (p2 → (p5 ∧ ((p3 → False) ∧ p3)))) ∨ ((p3 ∧ False) ∨ ((p2 ∨ p1) → True)))) := by
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
theorem thm_5_vars_106462554190650834408914340094 : ((((p1 → p1) ∨ (False ∧ (False → (p5 → p3)))) ∧ (False ∨ (((p1 ∨ (False ∨ p1)) ∧ p4) ∨ ((p5 ∧ (p3 ∧ p4)) → p5)))) ∧ (True ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648257558764900687168879866350 : (((((p4 ∨ (p4 → (False ∧ (p3 ∨ (True ∧ (True ∧ ((((False ∧ False) ∨ (p4 → (p2 → p5))) ∨ p4) ∨ False))))))) ∧ p5) ∧ (True → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122062334675649959764913953004 : (((p2 → (((((p5 ∧ ((p5 ∧ p4) ∨ (((p5 ∧ True) ∨ p2) ∨ p5))) ∧ True) ∧ p3) → (p4 ∨ False)) ∨ (p2 ∨ p1))) → False) → (p4 ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → (((((p5 ∧ ((p5 ∧ p4) ∨ (((p5 ∧ True) ∨ p2) ∨ p5))) ∧ True) ∧ p3) → (p4 ∨ False)) ∨ (p2 ∨ p1))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319163462601170078787342712406 : (p4 ∨ (((True ∧ ((((p4 → (True ∧ ((False → p2) → (p2 ∨ p5)))) → p3) ∨ p1) ∨ p4)) → p3) ∨ ((True → p2) ∨ ((False → p5) ∨ False)))) := by
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
theorem thm_5_vars_214133225385194964649162837275 : ((((p2 → True) ∨ p1) → p3) ∨ ((((((p1 → p4) → (p4 → p4)) → False) → ((((p5 ∧ p3) → p4) ∧ p4) → (False ∧ p2))) ∨ p3) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : ((p1 → p4) → (p4 → p4)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h5
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : ((p1 → p4) → (p4 → p4)) := by
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h14 := h1 h11
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137735422113932820987179847182 : ((p1 ∨ (p5 ∨ ((p3 → (((p4 ∧ ((p4 → (False ∨ False)) ∨ p4)) ∧ p2) ∨ True)) ∨ ((p4 ∧ (p1 → p1)) ∧ True)))) ∨ ((False → False) → p5)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213405725684792315086243773837 : (((p1 ∨ (True → False)) ∧ p1) ∨ ((((((p3 → p3) ∨ (((True → p1) ∧ p3) ∨ False)) ∨ p3) → p2) ∧ p4) ∨ (((p5 ∨ p2) → p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808009554177960480741706443510 : (((p4 → ((p5 → p1) → ((p4 → ((p1 ∧ (p5 → False)) ∨ True)) ∧ (p1 ∧ (((p1 → p2) ∨ ((p4 ∨ p1) → p4)) ∧ (p1 ∧ True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191070024135601258620141667274 : (((True → ((p4 ∨ p4) → p2)) → (p3 → (p3 ∧ p5))) ∨ (((p5 → ((p3 ∨ (p1 ∧ (p3 ∧ (p5 ∧ p2)))) ∧ True)) ∨ (p2 ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168939593100991115636088925245 : ((True → ((False ∨ (((p5 ∨ p2) ∧ True) ∧ p4)) → ((True ∧ ((p5 → p4) ∨ p2)) ∧ p3))) → (((False → p2) → ((True → p3) ∧ False)) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False → p2) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149008116837823254359124860520 : ((((p4 ∨ True) ∧ p4) ∨ ((((p4 ∧ p5) ∨ (p4 → (p2 ∧ False))) ∧ (False → p2)) ∨ ((p2 → p2) ∨ p2))) ∨ ((p3 ∨ (p4 ∨ p1)) ∨ p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356636728260121146441842227479 : (p5 → ((p1 ∨ (((p1 ∧ (p4 ∧ p5)) ∧ p1) ∧ p2)) ∨ (((p1 ∨ (p3 → p2)) ∨ (((p1 ∨ (p4 ∨ p1)) ∧ p3) ∧ (True → p2))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205001590013464291470353376564 : (((True ∨ (p5 → (p2 ∧ p2))) → p1) ∨ ((((p4 ∧ True) ∨ (p5 ∧ ((p1 ∧ False) → ((p1 → True) ∨ p5)))) → (p5 ∨ p5)) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692491984144180993682907288221 : (((((((p2 ∧ False) ∧ ((p5 ∨ p1) ∧ p2)) ∨ (False → p4)) ∨ (True ∧ p3)) ∧ (True ∨ (p1 → (((p5 ∧ p2) ∧ p4) ∨ (p1 ∧ False))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49037291925441417921326828383 : ((((p4 ∧ (((False ∨ (p2 ∨ False)) ∧ (True → (p2 ∧ ((True → (False ∧ (p1 ∨ p5))) → p4)))) ∨ True)) → False) ∨ ((p2 ∨ p1) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1688693372252710847959271766 : ((p4 → ((((True ∧ (p3 ∨ (True → (p3 ∧ p2)))) ∧ (p5 → p5)) → p1) ∨ (((p1 ∨ p3) → (p2 → False)) ∧ p2))) → (p2 → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309822434531889016073030073215 : (p2 ∨ ((p4 → ((p3 ∨ (True ∨ (((p1 ∨ (p4 ∨ (p4 ∧ p5))) → (False ∨ p4)) ∨ p5))) ∧ (False ∧ p2))) ∨ (p4 ∨ (p1 → (p3 → p3))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649637913875148723459627402626 : (((((((p5 → p5) ∧ p3) ∧ (p2 ∨ (True ∧ (((p2 ∧ ((True ∧ (p3 ∧ p5)) → p4)) ∨ p3) ∨ p2)))) ∨ (True → True)) ∧ (False → p5)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125042312319763297547335123597 : ((((True → p1) → p3) ∧ (((False ∨ (((p2 ∧ p5) → p4) → (True ∨ p3))) ∨ ((p5 ∨ False) → False)) ∨ ((True ∨ False) ∨ p3))) → (p4 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
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
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46242144620319245157678581540 : ((((True ∧ ((((p2 ∧ ((p5 ∨ p4) ∧ p4)) ∨ (True → p4)) → p1) → ((p1 → False) → (p5 ∧ True)))) ∨ (True → p2)) ∧ (p3 → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215256363364321809192718942080 : ((False ∧ (p3 ∧ (p1 ∧ p4))) ∨ ((((p2 ∨ (p4 ∨ ((p5 ∧ p5) → p1))) ∧ False) ∨ ((p5 ∧ (p1 ∨ p3)) → p5)) ∨ (False ∧ (p2 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137953920853783925719088260845 : ((p5 ∨ (((((p1 → (p3 ∧ True)) → True) → (True ∧ (p1 ∧ (False ∨ ((p1 ∧ (p4 → p2)) → p1))))) ∨ p4) → p5)) ∨ (True ∧ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340528741776642653152629272509 : (p2 → (((p3 ∧ (True → p2)) ∨ (((True → True) → p2) → (((((p3 ∧ False) ∨ p5) ∨ (((p1 ∨ p4) ∨ p2) ∧ p2)) ∨ p3) ∧ True))) ∧ p2)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59399215617594920790886176244 : (((True → p2) ∨ (p4 ∧ (p3 ∨ ((p1 → ((p2 ∨ (False ∨ ((p1 ∨ True) → (p1 ∨ (p4 ∨ False))))) ∨ p1)) ∧ ((p4 ∨ p5) ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54694119073145474611305483660 : ((((((p5 ∨ p3) ∧ p4) ∧ p1) ∧ (p3 ∨ p2)) → (p4 ∧ (p2 ∨ ((p3 ∨ True) → ((p3 → (p1 → ((p3 ∧ p2) ∧ p3))) → p2))))) ∨ p2) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- Implications on the right can always be decomposed.
      intro h23
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h24 =>
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h25 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h24
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h26 := h23 h25
        -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
        have h27 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h17
        -- We have shown the premise of h26, we can now drive its conclusion.
        let h28 := h26 h27
        -- We need to get the left conjuct of h28 based on <expert-advice>.
        let h29 := h28.left
        -- We need to get the right conjuct of h29 based on <expert-advice>.
        let h30 := h29.right
        -- One of the premise coincides with the conclusion.
        exact h30
      case inr h31 =>
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h32 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h21
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h33 := h23 h32
        -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
        have h34 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h17
        -- We have shown the premise of h33, we can now drive its conclusion.
        let h35 := h33 h34
        -- We need to get the left conjuct of h35 based on <expert-advice>.
        let h36 := h35.left
        -- We need to get the right conjuct of h36 based on <expert-advice>.
        let h37 := h36.right
        -- One of the premise coincides with the conclusion.
        exact h37
    case inr h38 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h38
  case inr h39 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h40 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h41
      -- Implications on the right can always be decomposed.
      intro h42
      -- Disjunctions on the left can always be decomposed.
      cases h41
      case inl h43 =>
        -- We want to use the implication h42 based on <expert-advice>. So we show its premise.
        have h44 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h43
        -- We have shown the premise of h42, we can now drive its conclusion.
        let h45 := h42 h44
        -- We want to use the implication h45 based on <expert-advice>. So we show its premise.
        have h46 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h17
        -- We have shown the premise of h45, we can now drive its conclusion.
        let h47 := h45 h46
        -- We need to get the left conjuct of h47 based on <expert-advice>.
        let h48 := h47.left
        -- We need to get the right conjuct of h48 based on <expert-advice>.
        let h49 := h48.right
        -- One of the premise coincides with the conclusion.
        exact h49
      case inr h50 =>
        -- We want to use the implication h42 based on <expert-advice>. So we show its premise.
        have h51 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h40
        -- We have shown the premise of h42, we can now drive its conclusion.
        let h52 := h42 h51
        -- We want to use the implication h52 based on <expert-advice>. So we show its premise.
        have h53 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h17
        -- We have shown the premise of h52, we can now drive its conclusion.
        let h54 := h52 h53
        -- We need to get the left conjuct of h54 based on <expert-advice>.
        let h55 := h54.left
        -- We need to get the right conjuct of h55 based on <expert-advice>.
        let h56 := h55.right
        -- One of the premise coincides with the conclusion.
        exact h56
    case inr h57 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h57



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198925514977845443333844647124 : ((p4 → ((((p4 ∧ False) ∧ p2) ∨ p1) ∧ p4)) ∨ (((((True ∨ (False → p3)) ∧ ((p4 ∧ True) ∨ False)) → p1) ∨ (True ∨ (p4 ∧ p5))) ∨ p5)) := by
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
theorem thm_5_vars_350220622162293216842832491454 : (p4 → (((False ∧ p5) ∨ (((p2 ∨ p3) ∨ ((False ∨ (p2 → True)) → (p3 → (p1 ∨ p1)))) ∧ (p2 ∨ (p3 ∨ (p2 ∧ (p4 ∧ p5)))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205848035176561331412838045559 : (((p2 → p5) → ((False ∧ True) ∧ p3)) ∨ (p3 ∨ ((p4 ∧ (p3 ∧ False)) → ((p3 ∨ p3) ∨ ((p5 → (p2 → ((p1 ∨ False) ∨ p2))) ∨ p2))))) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247709499055512165776896485687 : ((p1 ∨ False) ∨ (((((((False ∨ p1) → True) → ((False → p3) ∨ False)) → ((p2 → (p5 ∨ p2)) → (p2 → (p5 ∧ p1)))) ∨ p2) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314293847045576081155505563698 : (p3 ∨ ((((((p5 → p2) → (((((True ∨ True) ∨ (p5 ∨ True)) → p4) ∧ (p4 ∨ p2)) ∨ True)) ∧ True) ∨ p2) ∨ p4) → ((p1 ∧ p5) ∨ True))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
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
theorem thm_5_vars_54327934194275083064014979813 : (((p2 ∧ ((True ∧ p5) ∧ ((False ∨ p4) ∧ p3))) ∧ (p2 → (((p3 ∧ False) ∨ ((p5 ∧ (True ∧ (p5 ∨ p4))) → (p3 → p2))) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754261738046854629538575507809 : (((False ∧ ((p4 ∨ False) ∧ ((((p3 → p3) ∧ False) → (((p2 ∨ p1) → p3) ∧ True)) → ((((p5 ∧ True) ∧ True) → (False ∧ p2)) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66194609973356375946590924849 : ((p5 ∨ (((p2 ∧ ((True ∨ ((p4 ∧ p1) ∧ p3)) ∨ (True → True))) ∧ (p5 ∧ (p5 ∨ p4))) ∨ ((p1 → True) ∨ (p3 ∧ (p2 ∨ p2))))) ∨ p2) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186941504513799810692665295946 : (((p3 → (p4 → True)) ∧ (p3 ∨ ((False → p2) ∧ (p1 ∧ p4)))) → (True → (((p2 ∧ False) ∧ ((False ∨ p2) ∧ p3)) ∨ ((False ∨ True) ∨ p5)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67299113331120571522894443199 : ((p1 → (((((p4 ∨ p5) ∨ p4) ∧ (p1 → (p1 ∨ (p3 → (p3 → (p5 → False)))))) ∧ (p4 ∧ (((p5 ∨ True) ∧ p4) ∨ True))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111709706951445032535118449358 : ((((((True → (p5 ∧ (p2 ∧ (p5 → p3)))) → (p2 ∨ ((p1 ∨ p2) → p2))) ∨ (p5 ∨ ((p2 → False) ∨ p1))) → False) ∨ True) ∨ (p5 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137061837407960243749739542339 : (((p2 → p5) → ((True → (p4 ∧ p2)) ∨ (True ∨ (True ∨ ((p1 ∧ ((True → (p1 → (p1 → p3))) ∧ True)) → p5))))) ∨ (p3 ∧ (p3 → p5))) := by
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
theorem thm_5_vars_49161525174310500765241389142 : ((((((False → p1) ∨ False) ∨ (False ∧ p4)) ∧ ((p2 → p5) → (False ∧ ((p4 ∨ p2) ∨ (p2 ∧ (False → p5)))))) ∨ ((p4 → p4) ∨ p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39278279190294291999044732497 : (((p1 ∧ (((((p5 → (p2 ∧ (((False → True) → True) ∧ ((True ∧ p4) ∧ p1)))) ∨ (p4 ∧ p4)) ∨ (p4 ∨ p4)) → p3) ∨ True)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68475046346667185610118989528 : ((p3 → (p5 ∧ (((p5 ∧ (p2 ∧ (((p1 ∨ p4) ∨ True) ∧ ((p4 → p1) → p2)))) ∨ (p5 ∨ False)) ∨ ((True ∧ p3) → (p5 ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714339490425971153889933174702 : (((((p3 ∧ (p1 → p3)) ∨ (p4 ∨ p3)) → ((((p3 → False) ∧ (True → p2)) ∨ ((p1 ∨ (((p3 → p4) ∧ p3) ∨ True)) → False)) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178841391580775660133022028162 : ((((p3 → False) ∨ p4) → ((p2 ∧ True) ∧ ((p2 → (p5 ∧ True)) ∨ p3))) ∨ ((p4 ∧ p3) → (((p1 ∨ p3) ∧ (p2 ∧ (True ∧ p2))) → p3))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h4.left
    let h14 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h1.left
    let h18 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42693415197415745708906876138 : (((p5 ∨ ((p3 → (((True → ((False → ((p4 ∧ (p5 ∧ (False → p1))) ∧ p5)) ∧ ((p2 ∨ p3) → True))) → p5) ∨ p4)) → p5)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115807537748191183853490593663 : ((((True ∧ (p5 ∨ p5)) → p5) ∧ (p1 ∧ (((p2 → (((p1 ∧ (p3 ∨ p4)) → p4) ∧ False)) → ((p5 ∧ p3) ∧ True)) → p2))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43813561258734828852286655408 : ((((p3 → (((p4 → (p5 ∨ p4)) ∧ ((((p2 → (True ∧ p5)) → (True → (p4 → (p2 → False)))) → True) → p2)) ∨ True)) → p2) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149369535545004395550769558449 : (((p1 → True) → ((p5 ∧ ((p5 ∧ True) ∧ p2)) ∧ ((((p5 ∨ ((p2 ∧ True) ∨ p4)) → p2) ∧ True) ∨ p4))) ∨ ((p5 ∧ (False ∨ p2)) → p2)) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137817030655911605036441551928 : ((p3 ∨ (((((False → p4) → ((True → True) ∨ (((p1 → False) → p1) → False))) → p2) → ((True ∧ p5) ∨ p4)) ∨ p3)) ∨ ((p3 → p3) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621354061880559853442709232358 : ((((True ∧ ((p2 ∨ p2) → ((((p2 ∧ p5) → False) → True) ∧ (((p3 ∨ ((p5 → (p3 → p2)) ∧ p4)) → (p4 ∨ p5)) ∨ False)))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_345323701988238677368551394680 : (p3 → (((((((False → (p1 ∨ p3)) ∧ p3) → ((p3 ∧ (p3 ∧ ((False → (p3 ∨ False)) → p2))) ∧ False)) ∧ p2) ∨ (p1 ∧ p3)) ∧ p3) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119561186676297812652322803436 : ((p5 → (((((False → (p2 ∧ p2)) ∧ p4) → p3) ∨ (p1 ∨ (p2 ∨ p1))) ∨ (((p5 ∨ p5) ∨ p3) ∧ (False → (True ∨ False))))) ∨ (p1 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56024118103770201686567967700 : ((((False ∧ (p4 ∧ True)) ∨ p5) ∨ ((p1 ∧ (True ∨ p2)) ∨ (p2 ∨ ((p3 → ((p4 ∧ (p2 ∧ (p2 ∨ True))) ∧ True)) → (False → True))))) ∨ p5) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175469715406478801642647827251 : ((p2 → ((p1 → ((((p1 → p5) → p5) ∨ True) → p2)) ∨ (p4 ∧ (True ∨ p1)))) → ((((False ∧ (p5 ∧ (True ∧ False))) ∨ True) ∨ p5) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192476838845060613180675194731 : ((((True → (False ∨ (False ∨ p2))) → (True → True)) ∨ False) → ((p3 ∧ (((p4 → (p1 ∧ p2)) ∨ p5) ∨ (False ∨ (p5 → (p1 ∧ p3))))) ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247427862002026560730824352060 : ((False ∨ p2) ∨ ((p5 → (((p1 → p3) → ((False ∧ (p4 → (p4 → True))) ∨ (True → p4))) ∨ p5)) → ((p1 ∧ p3) → ((True → False) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116330177052884501267913004584 : ((((p3 ∨ p3) ∧ True) → (((p3 ∨ (((p3 → (p2 ∨ (p1 → p2))) ∨ True) ∨ p4)) → p4) ∨ (True ∨ (p1 ∧ (p4 → p3))))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233844047059011921451267442398 : ((p4 ∨ (p2 ∧ True)) → ((((p4 ∨ (True → (p5 → (p1 ∨ p4)))) → (p3 ∨ (p3 → p4))) ∨ (True ∨ (True ∧ (False → (True ∧ p5))))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311864592329567748726008847886 : (p2 ∨ (p2 ∨ (((p1 ∨ ((((True ∨ p5) ∨ p3) → ((p3 ∨ p4) → (((p3 ∨ True) → False) ∨ (p3 → p2)))) → p3)) ∨ (False → False)) ∨ p1))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248045300774578422043216495437 : ((p1 ∨ p5) ∨ ((p1 ∧ (p5 ∧ p3)) ∨ (((p3 ∨ True) → ((p1 → p4) ∧ ((True → p1) ∨ ((p3 ∨ (p4 ∨ True)) ∧ True)))) ∨ (p5 → p5)))) := by
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
theorem thm_5_vars_191457915559996958968256965290 : (((p3 → p3) → (p4 ∧ (p5 ∧ (p5 ∧ (p2 ∧ p1))))) ∨ (p2 → ((p3 ∧ True) → (((((False ∧ p2) ∨ p3) ∧ (p2 ∧ p3)) ∧ True) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h7.left
    let h13 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h2.left
    let h15 := h2.right
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54773044204518939421750150544 : (((True ∧ (p1 → (((p4 → p1) ∨ True) → p4))) → (((((((p1 ∨ (False ∧ p2)) → (p3 → p5)) → p1) ∧ p2) ∨ p2) ∧ p3) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699351896159049335302613384235 : ((((((p2 ∧ p4) ∧ ((p4 ∧ True) → ((p4 ∨ False) → p3))) ∧ p5) → ((p2 ∧ (((p5 ∨ p3) → (True ∨ True)) → (p1 ∧ p4))) ∨ p3)) ∨ p5) ∧ True) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h8 : (p4 ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h8
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : (p4 ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- One of the premise coincides with the conclusion.
  exact h11
  -- True on the right can always be proven directly.
  apply True.intro



