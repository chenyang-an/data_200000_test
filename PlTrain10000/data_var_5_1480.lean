variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49186268918906461887970802470 : (((((p1 ∨ p2) ∨ (p5 ∨ p5)) → (((p5 ∧ p5) ∨ (p4 ∧ p2)) → (((False → (p5 ∨ True)) ∨ p3) ∧ p4))) ∨ ((p3 ∨ True) ∨ p1)) ∨ p1) := by
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
theorem thm_5_vars_191946546452617919521785755109 : ((True → (False ∨ ((((p4 ∨ False) ∨ False) ∨ p1) ∨ True))) ∨ (True ∨ ((p4 ∧ False) → ((((p5 → p3) ∧ ((False → p3) ∨ False)) ∧ True) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254172353593255894210403490886 : ((p2 ∧ p1) → ((p3 → (((p2 ∧ p4) ∧ p2) ∨ (p5 ∧ (p4 ∨ p4)))) ∨ (p1 ∧ (False ∨ (p1 → ((p4 → p4) ∧ (True → (p4 ∨ True)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208363525552321267463698465158 : (((False ∧ p3) ∨ (p5 ∧ (p4 ∨ p5))) → ((True ∧ ((p1 ∧ True) ∧ ((True → ((p1 ∧ ((p5 ∧ True) ∨ (p2 ∧ True))) ∧ p2)) ∧ p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718073858370434892233059546786 : ((((((True ∧ p3) → False) ∨ p3) ∨ ((True → p1) → (p3 ∨ ((((p5 ∧ p1) → ((True ∧ True) ∨ (p2 → p2))) ∧ (p1 ∧ False)) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234076191962054322537335822941 : ((True → (p1 ∧ p1)) → (((p4 ∧ (True → ((p3 ∨ ((((p3 ∨ True) ∧ p2) ∧ (p1 ∨ p5)) ∧ p3)) ∨ (p1 ∨ False)))) ∨ (p5 ∨ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341115855252521307803724416879 : (p2 → (((((False ∨ (p3 → p5)) ∧ (((p2 ∨ (p3 ∧ (False → ((p4 ∨ (p3 → p4)) → (p1 → p4))))) ∨ True) ∨ p5)) ∧ True) ∧ p3) → p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
          have h14 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h4
          -- We have shown the premise of h10, we can now drive its conclusion.
          let h15 := h10 h14
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
          have h19 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h4
          -- We have shown the premise of h10, we can now drive its conclusion.
          let h20 := h10 h19
          -- One of the premise coincides with the conclusion.
          exact h20
      case inr h21 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h22 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h4
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h23 := h10 h22
        -- One of the premise coincides with the conclusion.
        exact h23
    case inr h24 =>
      -- One of the premise coincides with the conclusion.
      exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214502393546687885040308953785 : (((p3 ∧ False) ∧ (p4 ∧ p2)) ∨ ((False ∧ (((p2 → (p4 ∨ p2)) ∧ (p1 → ((False ∧ p1) ∧ p5))) ∨ ((p1 ∧ True) → p4))) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137315947624734911775067910217 : ((p2 ∧ ((p2 → ((True → (p1 ∨ p3)) ∧ p5)) → (p1 → (((True ∨ (p5 ∧ (True ∧ p1))) ∧ p5) ∧ (False ∧ True))))) ∨ (True ∨ (p5 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229002856758737525367279427212 : ((p5 ∨ (p2 ∧ True)) ∨ ((((True ∨ True) ∨ ((p1 → False) → p2)) ∧ True) → (((p4 ∨ p5) ∨ (False → (False ∧ (p4 ∨ True)))) ∨ (True → True)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190768887490046288182222441960 : ((((p1 ∧ (p5 ∧ (False ∨ p5))) ∧ True) ∨ (p5 ∧ p3)) ∨ (False → (((((p1 ∧ p5) ∨ True) ∧ p4) ∨ (False ∨ ((True ∧ p5) ∨ False))) → p1))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h1
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h1
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- False on the left can always be used.
        apply False.elim h1
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699566878531418016053544100372 : (((((((((p1 ∧ p2) ∨ False) ∨ p2) → (False ∧ p2)) ∧ p5) → p2) → ((p5 → (p4 ∨ p3)) ∨ (((p3 ∨ (p3 ∨ True)) → p2) → True))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_38533640320982324119094897173 : ((((p5 → (((True → (p1 ∧ True)) → p3) → (p3 ∨ (p2 → p4)))) → ((p1 ∨ p3) ∨ (p1 ∧ (((False ∨ p1) ∧ p1) ∧ False)))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338557677306258538273561551232 : (p1 → ((True → (p4 ∨ p5)) ∨ (p5 → ((True ∨ ((((p4 → p4) ∨ p5) → False) ∨ p3)) → (((p2 ∨ p3) ∨ p2) → (False ∨ (p4 ∨ p5))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172918102361819800600816215091 : ((p2 ∧ (p5 ∧ ((p4 ∨ (((p1 → ((False ∨ p3) ∨ p4)) ∨ p2) ∨ p2)) ∧ p4))) ∨ ((((((True ∧ p1) ∧ True) ∨ p2) → p1) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250034539254646611176733515407 : ((True → p3) ∨ (((p2 ∧ (p1 → p2)) ∧ (p2 ∨ ((p4 ∨ (((False → p4) → ((p4 ∧ p3) ∨ p3)) ∧ p2)) ∨ True))) ∨ ((True ∨ False) ∨ p3))) := by
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
theorem thm_5_vars_216595202651164209021057668667 : ((((False → False) ∧ p1) ∧ p5) → ((((p2 ∨ (p2 ∨ p4)) ∧ p3) ∧ (p4 ∨ p1)) → (False ∨ ((p4 ∨ ((False ∧ p5) ∧ p3)) → (True ∧ p4))))) := by
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
    cases h4
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h1.left
      let h10 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Conjunctions on the left can always be decomposed.
        let h18 := h16.left
        let h19 := h16.right
        -- False on the left can always be used.
        apply False.elim h18
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h1.left
      let h22 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h21.left
      let h24 := h21.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h25
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- One of the premise coincides with the conclusion.
        exact h26
      case inr h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- Conjunctions on the left can always be decomposed.
        let h30 := h28.left
        let h31 := h28.right
        -- False on the left can always be used.
        apply False.elim h30
  case inr h32 =>
    -- Disjunctions on the left can always be decomposed.
    cases h32
    case inl h33 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h1.left
        let h36 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h37 := h35.left
        let h38 := h35.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h39
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Disjunctions on the left can always be decomposed.
        cases h39
        case inl h40 =>
          -- One of the premise coincides with the conclusion.
          exact h40
        case inr h41 =>
          -- Conjunctions on the left can always be decomposed.
          let h42 := h41.left
          let h43 := h41.right
          -- Conjunctions on the left can always be decomposed.
          let h44 := h42.left
          let h45 := h42.right
          -- False on the left can always be used.
          apply False.elim h44
      case inr h46 =>
        -- Conjunctions on the left can always be decomposed.
        let h47 := h1.left
        let h48 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h49 := h47.left
        let h50 := h47.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h51
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Disjunctions on the left can always be decomposed.
        cases h51
        case inl h52 =>
          -- One of the premise coincides with the conclusion.
          exact h52
        case inr h53 =>
          -- Conjunctions on the left can always be decomposed.
          let h54 := h53.left
          let h55 := h53.right
          -- Conjunctions on the left can always be decomposed.
          let h56 := h54.left
          let h57 := h54.right
          -- False on the left can always be used.
          apply False.elim h56
    case inr h58 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h59 =>
        -- Conjunctions on the left can always be decomposed.
        let h60 := h1.left
        let h61 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h62 := h60.left
        let h63 := h60.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h64
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Disjunctions on the left can always be decomposed.
        cases h64
        case inl h65 =>
          -- One of the premise coincides with the conclusion.
          exact h65
        case inr h66 =>
          -- Conjunctions on the left can always be decomposed.
          let h67 := h66.left
          let h68 := h66.right
          -- Conjunctions on the left can always be decomposed.
          let h69 := h67.left
          let h70 := h67.right
          -- False on the left can always be used.
          apply False.elim h69
      case inr h71 =>
        -- Conjunctions on the left can always be decomposed.
        let h72 := h1.left
        let h73 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h74 := h72.left
        let h75 := h72.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h76
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Disjunctions on the left can always be decomposed.
        cases h76
        case inl h77 =>
          -- One of the premise coincides with the conclusion.
          exact h77
        case inr h78 =>
          -- Conjunctions on the left can always be decomposed.
          let h79 := h78.left
          let h80 := h78.right
          -- Conjunctions on the left can always be decomposed.
          let h81 := h79.left
          let h82 := h79.right
          -- False on the left can always be used.
          apply False.elim h81



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171420898677256615290540985836 : ((((p2 ∧ False) ∧ ((p2 ∧ ((p5 → p3) → (p1 → (p5 → p5)))) → p1)) ∧ p5) ∨ (p2 ∨ ((p2 ∨ True) ∨ ((p2 ∧ (False → p5)) ∨ p4)))) := by
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
theorem thm_5_vars_299362711927883440614275884960 : (False ∨ (((True → p2) ∧ (p4 ∨ (p4 ∧ ((p3 ∨ (p4 ∧ p1)) ∨ (((p1 ∧ (True → p1)) → p1) → (p1 → ((p4 ∧ p3) → True))))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197729537492957664104023397937 : ((((p3 ∨ p3) ∨ p3) ∧ (True ∨ (p2 → p4))) ∨ ((p2 ∨ (False ∨ p5)) ∨ ((((((False ∨ (False ∧ p2)) ∧ p5) ∨ p2) → p4) ∨ True) ∨ p1))) := by
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
theorem thm_5_vars_764176553336452195611576707999 : (((p3 ∧ (p5 → ((((False ∨ p3) ∧ p2) → ((p2 ∨ p3) → ((p2 ∧ p3) → ((p2 ∨ ((p4 ∨ p1) ∨ True)) ∨ True)))) → (p4 ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690919035184196380962134606501 : ((((((((p4 ∧ (True ∨ p2)) ∧ (p2 → (p5 → True))) → p5) ∨ True) ∨ (False ∧ False)) → (p4 ∧ ((p4 ∨ (p3 → p3)) ∨ (p4 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355303624039801699261632168022 : (p5 → ((p1 ∧ ((((p4 → (p1 ∨ (p5 ∧ p2))) → (((p5 ∧ p3) → False) ∨ p3)) ∨ p5) → ((False ∧ (p3 → (p5 ∧ p4))) ∧ p2))) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (((p4 → (p1 ∨ (p5 ∧ p2))) → (((p5 ∧ p3) → False) ∨ p3)) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340908551536034194224336198073 : (p2 → (((((p2 ∨ p4) ∧ (p3 ∨ p3)) → ((p4 → p4) ∨ p3)) → (((p2 → ((True ∧ p2) → p4)) ∧ p4) ∧ ((False → False) ∨ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608828069037446764567818351784 : ((((((((((p3 ∨ False) ∨ p1) → ((p5 ∧ (p1 ∨ (p1 ∧ False))) → p5)) ∧ p5) → p2) ∧ (False ∨ ((p4 ∨ True) → p3))) ∨ True) ∨ False) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_208875062942773755073921691570 : ((p4 ∧ ((p3 ∨ p4) → (False → p5))) → (((p2 ∨ ((p2 ∨ False) ∧ False)) ∨ (p2 ∨ True)) ∨ (((p1 → (p1 ∨ False)) ∨ (p4 → p3)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213087001688932153876815669748 : ((((p4 ∧ False) ∧ p5) ∧ False) ∨ (p5 ∨ (((True ∨ (True ∨ p4)) ∨ (True ∧ ((False ∨ p2) → ((p3 → p3) ∧ False)))) ∨ ((p1 ∧ False) → p2)))) := by
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
theorem thm_5_vars_138238752834773374509271618460 : ((p2 → (((p5 ∨ (p2 ∧ (p1 ∧ (p5 ∨ True)))) ∧ p1) ∨ ((False ∧ (p2 → (p5 ∨ (False → p5)))) ∨ (p3 ∨ True)))) ∨ (p5 ∧ (p1 → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799602651903109836908424260186 : (((p1 → (p5 ∨ ((True ∧ ((((((p4 ∨ p1) ∨ p2) ∧ p2) ∨ (((True ∨ p5) → False) ∧ ((p4 ∨ p3) → True))) ∨ p1) ∨ True)) ∨ True))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181485453831600644857499708018 : ((p4 ∨ (p4 → ((p1 → (False ∨ p3)) ∨ ((False ∧ (p5 ∧ p5)) ∧ p1)))) → (((p2 ∧ (True ∧ (p1 → (p2 → (True ∧ False))))) ∨ True) ∧ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707582724106212927928813991854 : (((((p2 ∧ p3) ∧ ((p4 ∨ True) → (p2 → p2))) ∨ ((p2 ∨ (p5 → (p1 → p2))) ∨ ((p4 ∨ True) ∨ (p3 ∨ (p4 ∧ (p5 ∨ p5)))))) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156728503781109905534813678389 : (((((((p3 ∨ p5) ∨ p2) → p4) ∧ True) → (p4 ∨ (p5 → ((True → (p5 ∧ p1)) ∨ p1)))) ∧ p3) ∨ (p5 ∨ ((p5 ∧ p1) ∨ (True ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64143231428719762683041487728 : ((False ∨ (((p2 → p4) ∧ p3) ∨ (p5 → ((False ∨ (p3 ∨ (p2 ∨ p5))) ∧ (p5 ∨ ((True ∧ True) ∨ ((False ∧ (p3 ∨ p3)) ∨ p1))))))) ∨ p1) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64440283577041743430576202119 : ((p1 ∨ (((((p2 ∨ (((p3 → p3) ∨ p3) → p4)) ∧ True) ∧ False) ∧ (((p3 → p1) ∨ (p2 ∨ (True ∨ p2))) → True)) ∨ (False ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185679540782536417615903016662 : ((p1 → (((p3 → p4) → (p4 → False)) ∨ ((p1 → False) → p3))) ∨ ((((((p3 → p3) ∧ (True ∨ (p3 ∨ False))) → p5) ∧ p4) ∧ p2) ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620432385734434867520762038189 : (((((p5 ∨ p4) ∨ ((((p1 ∧ p5) ∨ (p5 ∨ (p4 ∨ ((p5 → True) ∨ (p5 → (p4 ∨ False)))))) ∨ ((p3 → p5) ∨ p5)) ∨ p1)) ∨ p1) ∨ p1) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49785120323138637443702136273 : (((p3 ∨ (False → (((((p1 ∧ (p2 ∧ (p2 → (p3 ∧ False)))) ∧ False) ∨ (p1 → False)) → p1) ∨ (True → True)))) → (p1 → (p4 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137088085250958584898433093234 : ((True ∧ ((((p4 ∧ p1) ∨ (p1 ∨ (((p3 → (p5 ∨ p5)) ∧ p4) ∧ (p4 ∧ (False ∧ (p2 ∧ p5)))))) ∨ True) ∨ p5)) ∨ ((p3 ∧ p4) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_41681918908445727807059892986 : ((((p1 ∧ ((p3 → p3) ∧ (p5 ∧ False))) ∨ ((p2 ∨ p2) ∧ ((p3 ∧ (((p5 → p2) ∨ ((p4 ∨ p2) ∨ p4)) ∧ p2)) ∧ p4))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595851540150306230228005858269 : ((((((((True ∨ p5) ∨ (p5 → (p5 ∨ p5))) → p1) ∧ p4) ∨ (((p4 ∧ p1) ∨ (False ∧ ((p4 → (p3 → False)) ∨ True))) ∨ True)) ∧ True) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186425734805396440291771638027 : (((True → (p2 ∧ (False ∧ (p1 ∧ ((p5 → p5) ∧ p4))))) → p3) → ((p3 → p1) ∨ (((True ∨ p4) ∨ (False ∧ (p3 ∨ (True ∨ p3)))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_64404221121260207862166455754 : ((p1 ∨ ((((((p2 ∧ True) ∨ (p3 ∨ False)) ∧ (p3 ∨ p2)) ∧ p4) ∨ (((p3 ∨ p1) ∨ (p3 ∧ ((p3 ∧ p2) → p4))) ∧ p5)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214517793987493973984497482166 : (((p4 ∧ p3) ∧ (True ∧ p5)) ∨ ((p2 → (p1 → ((p2 ∧ ((p4 ∧ p4) → (p1 ∧ (p3 ∧ (p4 ∧ p5))))) ∨ ((p2 ∨ p5) ∨ p1)))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167285911898985999803850693198 : (((((p3 ∨ p5) ∧ ((True ∧ p3) ∧ ((p5 ∨ p1) ∧ (p5 → (False ∧ p5))))) ∨ p5) → p1) → (((p1 → p4) ∧ ((True ∧ p4) ∧ True)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225262584413243224582064614074 : (((True ∨ p1) ∧ p5) ∨ (((((p2 ∧ p5) → p1) ∨ p2) ∨ ((p1 ∨ (False → ((False → p4) → True))) ∨ p4)) ∧ ((False ∨ (True → True)) ∨ True))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179261207583853042353659592275 : ((p5 ∧ (p2 → ((True ∨ (True → (((p4 ∧ p3) ∧ p2) ∨ False))) → False))) ∨ (((p4 → p2) ∨ (((p5 ∧ p4) ∨ p4) → (True ∨ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42214196698160351639789062507 : (((False ∧ (((p2 → ((((((((True ∧ (p3 → False)) ∧ p5) ∨ p1) ∨ p5) ∧ p5) ∨ False) ∧ p5) ∨ (p2 ∧ p3))) ∧ p3) ∨ p5)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307259344077138560094889156798 : (p1 ∨ (p2 ∨ (((p2 ∧ (p4 ∧ p4)) ∧ (True ∧ (True ∨ ((p5 → (p5 ∧ (p4 ∨ p2))) → (p4 → True))))) ∨ (((False ∨ True) ∨ p5) ∨ p3)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252289687438777157159204179274 : ((p4 → p5) ∨ ((p3 ∨ ((p5 → (True ∧ (p4 ∧ p1))) ∨ (p1 → p2))) ∨ (False → ((p1 ∨ (p1 → ((p5 → False) ∨ (False ∧ p4)))) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68144607952625985623860590615 : ((p3 → ((((True → (p4 ∧ p5)) ∧ ((True ∨ ((p4 ∧ p3) ∧ (p3 ∨ p2))) → (p5 → (p1 ∧ (p4 → p2))))) ∨ (p1 → p2)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300800880161635754086646163505 : (False ∨ ((p5 → ((((p4 ∨ True) ∨ (False → (p2 → p1))) ∧ (p4 ∨ p4)) ∨ (False ∧ p1))) ∨ (False → ((((False ∨ p3) → p2) ∧ p1) → p3)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42210924969371176163809226745 : (((False ∧ (((((p4 ∧ ((p3 ∧ (((p2 → (False → p1)) → p4) ∧ p1)) ∧ (p2 ∨ (p2 → p2)))) ∨ p4) ∨ False) → False) ∧ p3)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7955344252204791819302689526 : (((((p1 ∧ (p1 → (((p1 → (p3 → p1)) → (False ∨ p2)) ∧ ((((False → p4) ∨ p2) → (p1 → p5)) ∧ p4)))) ∧ p1) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_207682541308002312929880678973 : ((((p4 ∧ True) → (p5 ∨ True)) → p5) → (((p2 → p4) ∧ p1) ∨ ((((False ∧ (True → p5)) → (False → True)) → True) ∧ ((p5 ∧ p2) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342237418912626807899443963177 : (p2 → ((((p4 ∧ p1) ∧ (p1 ∧ ((p4 ∨ (((p2 → p3) ∨ p1) ∨ (p3 ∧ p3))) ∧ p2))) ∨ p2) ∧ ((p5 ∧ (p4 ∨ p4)) → (p2 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301398594170053729802540339545 : (False ∨ ((True → (True ∧ (False ∨ p5))) ∨ (p4 → ((((p1 ∧ ((False ∨ p3) ∨ True)) ∨ ((True ∨ (p4 ∧ p3)) → p2)) ∨ (False → p2)) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157101212825960362471195462082 : (((p2 → (((((p4 ∧ p4) ∨ p5) ∨ p2) → (p5 → (p2 → (p1 → (True ∨ p1))))) → False)) ∨ True) ∨ ((((False ∨ p5) ∨ p4) → p2) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54782176440108492154279518127 : (((p2 ∧ ((p5 → (p5 → p5)) ∨ (p3 ∧ p1))) → (p2 → (((True ∧ p3) → False) ∨ ((((False ∨ p5) ∧ p5) → (p2 ∧ p4)) ∨ True)))) ∨ p3) := by
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
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37477384415610298629137424813 : (((((((True ∨ False) ∧ p2) → p3) ∧ (p1 ∧ ((((p2 ∧ ((p1 → p5) ∧ p1)) ∨ p4) ∧ False) ∨ ((p1 ∧ p4) ∧ p3)))) ∨ p5) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666489083415250610710159204142 : ((((((p4 → p1) → (((p5 ∧ p1) ∧ (((p3 → p1) ∧ True) ∧ p4)) → False)) ∧ ((True → (p4 → p1)) ∧ p1)) ∧ ((p5 ∨ False) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38726120926862368204524187597 : ((((((p3 → p1) → False) → (p4 ∧ p5)) → (((p1 → p1) → p4) ∨ (True → ((True → p4) → (p2 ∨ ((False ∧ False) → True)))))) ∧ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349211800348783868280450027409 : (p3 → (p1 → ((((((p2 → False) ∨ False) → p2) ∨ (((p4 → p3) → p4) → (p5 → ((False ∨ p4) ∧ ((p2 → p5) → True))))) ∧ p1) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p4 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328639680222979711328878489265 : (True → (((((p4 → p3) → p5) → (p5 → ((p4 → p5) ∨ (p3 ∨ p3)))) → p1) → ((p3 → ((p3 → ((p2 ∧ p5) ∨ p3)) ∨ False)) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p4 → p3) → p5) → (p5 → ((p4 → p5) ∨ (p3 ∨ p3)))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184665624591297694810430165001 : ((((p2 ∧ p3) ∧ (p1 → (p1 ∧ p2))) ∨ ((p1 ∨ p5) ∨ True)) ∨ (True → (p2 ∨ ((False → (((p3 ∨ p4) ∧ p2) → (False → p1))) ∨ True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1522681360152173815863518725 : (((p4 → (p5 ∧ (p3 ∧ p5))) ∧ (p2 ∨ (((p4 → ((p4 → False) ∨ (p3 → p3))) ∧ (False ∨ (p2 → False))) ∧ False))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304903078251774660742221272732 : (p1 ∨ ((p2 → ((False ∨ (((p3 ∨ (True ∧ (True → (p5 → p3)))) ∨ p2) ∨ p2)) → ((p3 ∨ (True ∨ (p2 ∨ p3))) ∧ False))) → (p2 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (False ∨ (((p3 ∨ (True ∧ (True → (p5 → p3)))) ∨ p2) ∨ p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159723333023290072334107741587 : ((((((p5 ∧ p1) ∧ p4) ∧ ((p2 → True) → p1)) ∧ ((True ∨ ((p1 ∧ p3) ∧ p4)) ∨ True)) ∨ p1) → (((True → (p4 → p2)) ∨ p1) ∨ p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Conjunctions on the left can always be decomposed.
        let h16 := h14.left
        let h17 := h14.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h19 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194799589173578910835924917335 : (((p2 → (True → (p2 ∨ (p4 ∧ p1)))) ∨ p4) ∧ (((p5 ∨ p2) ∨ (True → (p1 ∧ False))) ∨ (False ∨ ((False ∧ False) → ((p3 → p3) → True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117818115129594131817857713673 : ((p4 ∧ ((p1 → p3) → (((p4 ∧ p4) → (((((p2 → (True ∨ True)) ∨ p1) ∨ p1) → p3) ∧ p2)) ∧ (True ∨ (p1 ∧ True))))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615678851686524417778659133447 : (((((((True → (((p4 ∨ (False → p2)) → True) ∧ p5)) ∨ p1) → (p2 → p4)) ∧ ((p1 ∧ p5) → ((p1 ∨ p3) → (True ∧ p4)))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_167251873994769283047959910688 : (((((p4 → ((((p4 ∨ p2) → p3) ∨ ((False ∧ False) ∨ True)) ∧ True)) ∧ p3) ∧ p4) → p3) → ((((p5 ∨ p2) ∧ (p5 → False)) ∧ p5) → p2)) := by
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
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44820800072432245610470325219 : ((((True → (p1 ∧ p4)) ∧ (p5 ∨ (p2 ∧ ((((p4 ∧ p2) ∧ p2) ∨ ((p5 ∨ False) ∨ ((p3 ∧ False) → (False ∧ True)))) ∧ p1)))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165599947047490429615737725500 : ((((((False ∧ p1) → p2) → p5) ∧ (p5 ∨ p5)) → ((False ∧ ((p1 → p1) → p1)) ∨ p4)) ∨ (True → ((False → (p4 ∨ True)) ∧ (False → True)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308415389932609620406410383169 : (p2 ∨ (((((p1 ∧ ((False ∧ p1) ∧ p4)) ∨ ((p2 → (p3 ∨ True)) ∨ ((((False ∧ False) ∨ p5) → (p4 → False)) → p4))) → False) → p2) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∧ ((False ∧ p1) ∧ p4)) ∨ ((p2 → (p3 ∨ True)) ∨ ((((False ∧ False) ∨ p5) → (p4 → False)) → p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673414307556263232172691510627 : (((((p4 → (p3 ∨ (False ∨ (True ∧ False)))) → (((((False ∧ p2) ∧ ((False → p1) → False)) ∧ False) ∨ p1) ∧ p5)) → (p4 ∨ (p5 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135292837278509400372321747787 : ((((((p1 → (False ∨ (p5 ∨ ((p5 ∧ False) ∧ False)))) → (False ∧ (p3 ∧ p3))) → False) ∧ p5) ∧ (p4 ∨ (p5 ∨ p4))) ∨ (False ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103053402696678711291763175903 : ((((((p4 ∨ (p4 ∨ p3)) → True) ∧ p3) → ((p3 ∧ ((p4 ∧ False) → p2)) → (True ∧ (False ∧ (p4 ∧ (p5 ∧ p2)))))) ∨ True) ∧ (True ∨ True)) := by
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
theorem thm_5_vars_173453268004442340254837110550 : ((((p5 ∨ ((p3 → (p3 → True)) ∨ (True ∧ (True → (p1 ∨ p1))))) ∧ p5) ∧ p5) → (p2 ∨ (((p3 → p5) → (p4 ∧ p3)) ∨ (p1 → p5)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206635882509248385147605866394 : ((p1 → ((p5 ∨ p5) ∧ (True ∧ p3))) ∨ (p4 → ((True ∧ ((p1 → p2) → p1)) ∨ (p4 ∨ (((p2 → p1) ∧ p2) ∧ ((False → True) → p3)))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148824075705895946407444105685 : (((p3 ∨ ((p2 ∧ p4) ∨ (p5 ∧ p3))) → (((((p5 ∧ (p5 → (False ∨ p2))) ∧ False) ∧ False) ∨ p2) ∧ p4)) ∨ (((p1 ∨ p3) ∧ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727264432728273920871797430528 : ((((p1 ∧ (False ∧ p2)) ∨ (p2 ∨ (((((False ∧ (p5 ∨ (True ∨ ((False ∧ p5) → p3)))) ∧ p2) ∧ p4) → ((True ∨ p1) → True)) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206345404033807191482686116178 : ((p2 ∨ ((False ∨ (False ∨ p2)) ∨ p1)) ∨ (((((p5 ∧ (p5 ∧ p1)) → (p5 → p4)) ∧ ((p3 ∧ (p2 ∧ (p4 → p2))) ∨ p4)) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252992615825152832509033100994 : ((True ∧ p3) → ((p2 → (((((p3 → (False → False)) → p1) ∨ ((((False ∨ (p2 ∨ p5)) ∨ p4) ∨ (p4 → p2)) ∨ True)) → p5) ∨ p2)) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51191069325898110777023484965 : ((((p1 → ((p4 ∨ (p5 ∨ False)) ∧ ((True ∨ (False → False)) ∨ p4))) ∨ (p3 ∧ (p4 → False))) ∨ (((p2 ∧ p5) → p2) → (p3 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118605263961253809396217388085 : ((p4 ∨ ((((((p2 ∧ True) → False) ∧ ((p1 ∧ False) ∨ (False ∧ p5))) → p5) → ((p2 ∧ p2) ∨ False)) ∨ (False → (p4 → p3)))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745353759757373220083642661131 : ((((p5 ∧ p3) → ((((p3 ∧ p2) ∧ p5) ∨ ((False ∧ ((False ∨ p4) ∨ (((p1 ∧ p3) → p2) ∨ (False ∧ True)))) ∨ (p3 → p3))) ∨ p2)) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253891336767865143829653191239 : ((p1 ∧ p3) → (p4 ∨ (((p4 → ((p3 ∨ ((p4 ∨ p1) ∧ p5)) ∨ (False ∨ p4))) → ((p2 ∨ p4) → p5)) ∨ ((p2 ∨ (True ∨ p2)) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103159351611731769178665391509 : ((((p4 ∨ False) ∨ (((p2 ∨ (((p4 ∨ ((True ∧ p2) ∨ p4)) → (True → ((p5 → p5) ∨ True))) → p5)) → p4) ∨ True)) ∨ True) ∧ (True → True)) := by
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
theorem thm_5_vars_600626785319640924476791505031 : ((((False ∧ ((p2 ∨ (True → ((p2 → (False ∨ ((((False ∧ p5) ∨ True) ∧ p3) ∧ True))) ∧ (p4 → ((False → True) → p3))))) ∧ p4)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190102030381385296485946471097 : ((((((True ∧ False) ∨ p5) → p2) → (p4 ∨ p1)) ∧ False) ∨ (p1 → ((p2 → True) ∨ (((True → (p2 ∨ p5)) ∨ p1) ∧ (True → (p4 ∧ p1)))))) := by
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
theorem thm_5_vars_356013641425424209239004987637 : (p5 → ((((True ∧ ((((False → p4) ∧ True) → (p4 → False)) ∨ p3)) ∧ ((p4 ∧ p5) ∧ (p5 ∨ p1))) ∨ p2) ∨ ((p4 ∨ p3) → (p5 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133664475251327721060749548559 : ((((p5 ∨ (p3 ∨ ((True ∧ ((False ∨ False) → ((p1 ∧ ((p4 ∧ p2) ∨ p4)) ∨ False))) → p5))) ∨ (p1 → p3)) ∧ p1) ∨ (p5 → (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136574630534103129488678605124 : ((((p3 → False) → p2) ∨ ((p1 → ((((((True ∧ p4) → (True → p1)) → p2) ∧ p4) ∨ p4) → (False ∧ True))) → p2)) ∨ (True ∧ (True ∨ True))) := by
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
theorem thm_5_vars_662102517038740966784706444320 : ((((((p4 ∧ (p4 → (p4 ∨ p3))) ∧ (((p3 → p3) ∨ p3) ∧ p5)) ∨ (True → (p3 ∧ (((p5 → p5) ∧ p5) ∧ False)))) → (p5 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188271831199516245349658194125 : (((False ∨ (((p3 → (p2 ∧ p4)) ∧ p3) → False)) ∨ True) ∧ (p5 ∨ ((False → False) ∨ (False ∧ ((p4 → p5) ∧ ((False → p2) → (p5 ∨ False))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39200192351460800085575093252 : (((True ∧ (((p2 ∨ ((p3 ∧ ((p2 ∨ (p2 → ((p4 → (p1 ∧ p2)) ∧ p5))) ∨ p5)) → p5)) ∨ ((p3 ∨ p3) ∨ False)) ∨ False)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55923068731186629054090548604 : (((False → ((p4 → False) → p4)) ∧ ((((p2 ∧ p2) ∧ (False ∨ (p3 → False))) → p4) → (p1 → (((p3 → (p4 ∧ False)) → p4) ∨ p1)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314227875340831615261384360505 : (p3 ∨ (((((((True → ((True ∧ p5) ∧ p3)) → p4) ∨ (((p3 ∨ p5) → p2) → p1)) ∨ (False → p5)) ∨ p3) ∨ p4) ∨ ((p1 ∨ p5) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48379391057429699995984032910 : (((True → (((p1 → ((p2 → (p4 → (p1 ∧ True))) ∨ p1)) → ((True ∧ (p1 → p1)) ∨ (p5 ∨ p2))) ∨ (p3 ∨ p5))) → (p2 ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60241598399194329314392798120 : (((True → p5) → ((p4 ∧ (p4 → False)) ∧ (((((True ∨ False) → (p5 ∨ (p5 → False))) ∨ p2) ∧ ((p4 → (p4 ∧ False)) ∧ p4)) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



