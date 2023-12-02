variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42856457916604881064104726126 : (((p2 → ((((((p1 ∧ (p1 ∧ (False → p2))) ∧ (True → p4)) → False) → p4) ∧ (p2 ∨ p1)) ∨ (p5 ∨ (False ∨ (p3 ∨ p2))))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167222698873155757286141447992 : (((p4 ∨ ((p5 ∧ (True ∨ (p4 ∧ p5))) ∧ (((p3 ∧ p1) ∨ (p2 → True)) ∨ p5))) ∨ p4) → (((p1 ∨ (p2 ∨ True)) ∧ (p1 ∨ True)) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- Conjunctions on the left can always be decomposed.
            let h12 := h11.left
            let h13 := h11.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- Conjunctions on the left can always be decomposed.
            let h21 := h20.left
            let h22 := h20.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h23 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h25 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738562844443196835300237893747 : ((((p1 ∧ p5) ∨ ((p2 → (False ∨ p4)) ∨ (p4 ∨ (p4 → (((p4 ∨ ((p5 ∧ True) → ((p3 ∧ (p4 ∨ p4)) ∨ p4))) ∨ p4) ∨ p1))))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136674516474672811274206624043 : (((p5 ∨ (p3 ∧ True)) → ((((((False ∧ p5) ∨ (p2 ∨ p1)) ∧ (True ∨ p2)) ∨ (p4 → p3)) → (p4 ∨ p5)) ∧ False)) ∨ ((True → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60396414361579529437111442549 : (((p3 → p5) → (((p1 ∨ (((False ∧ (True → p4)) ∨ ((True ∨ p3) ∧ p2)) ∧ p1)) → ((False ∧ True) ∨ (p5 ∨ (p3 → p2)))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342696580731441042892871897245 : (p2 → (((p1 ∨ False) ∧ (((False ∨ p2) → (p4 → p1)) ∧ p3)) → (((((p1 → (p4 ∧ (p1 → p2))) ∧ True) ∧ p1) ∨ (p2 → False)) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159848930375795550353814147325 : (((p2 → ((False ∨ ((p2 ∧ (False → p4)) ∨ ((p3 → p1) ∧ p5))) ∧ (p1 → (p2 ∧ False)))) ∨ p5) → (((p3 ∧ p1) ∨ (True ∧ True)) ∨ p2)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
theorem thm_5_vars_136757223697912233706283297209 : (((p3 ∨ True) ∧ (((((False ∨ ((((p1 ∧ p1) → p5) ∨ p2) → (p1 ∧ p3))) ∨ p4) → p5) → p2) ∨ (p5 → p3))) ∨ ((p1 ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45014051441402567995915291883 : ((((p4 ∧ p5) ∨ ((((p4 → ((p2 → p2) ∨ (p1 ∧ p2))) ∨ p4) ∨ (p5 ∧ False)) → (p5 ∨ (((False ∧ p2) ∧ True) → p3)))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_851624127919796162053462286086 : ((((True → ((((((p2 → ((False ∧ (p2 ∧ True)) → (p5 → (p4 → p1)))) ∨ p2) ∨ p1) ∧ (p4 ∨ p5)) ∨ p1) ∧ (False ∧ False))) ∨ p1) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- We need to get the right conjuct of h4 based on <expert-advice>.
    let h5 := h4.right
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172249016488332181567607303698 : (((False ∧ ((p5 ∧ True) ∧ (p5 → (p3 ∧ p3)))) ∧ (((True → p4) → p2) ∧ False)) ∨ ((((p4 → p2) ∨ p1) → ((True → p3) → p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350221423726568462383726974160 : (p4 → (((p2 ∧ p2) ∨ (((p5 → (((False ∧ p1) ∨ p4) → (True ∧ p1))) ∨ ((p1 → (False → p3)) → (True → (False ∨ p1)))) ∨ p4)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341841695413616560645952256194 : (p2 → ((((p1 ∨ (p4 ∧ p3)) ∨ p5) ∧ (((p1 ∨ (p5 ∨ ((p2 ∨ p3) ∨ p1))) ∨ (p1 → False)) → (False ∧ (p2 ∨ p2)))) → (True ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h7 : ((p1 ∨ (p5 ∨ ((p2 ∨ p3) ∨ p1))) ∨ (p1 → False)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h8 := h4 h7
      -- We need to get the left conjuct of h8 based on <expert-advice>.
      let h9 := h8.left
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h13 : ((p1 ∨ (p5 ∨ ((p2 ∨ p3) ∨ p1))) ∨ (p1 → False)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
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
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h14 := h4 h13
      -- We need to get the left conjuct of h14 based on <expert-advice>.
      let h15 := h14.left
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h17 : ((p1 ∨ (p5 ∨ ((p2 ∨ p3) ∨ p1))) ∨ (p1 → False)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h18 := h4 h17
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205320032058617521303084387973 : (((p5 ∨ (p3 ∧ False)) ∨ (p1 ∧ p2)) ∨ ((False → (((((p3 → True) → (p5 ∨ (False ∧ p4))) ∨ (True ∧ False)) ∧ (p1 → True)) ∨ True)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190663655125548428106787230428 : (((True → ((p2 → (False ∧ p3)) ∨ (p3 ∨ True))) → p1) ∨ ((p4 ∧ False) ∨ ((p4 ∧ False) ∨ ((p3 → ((True ∨ p3) ∧ (False → p1))) ∨ p1)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53096011807514044867405864859 : (((p3 ∨ ((p2 → p3) ∧ (((p5 ∨ p4) → (p3 → p2)) → p4))) ∧ (p1 ∧ (p4 → (((True ∧ ((p2 ∨ p2) ∨ p4)) ∨ p3) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172420203671162407045102934984 : ((((p4 ∨ p5) ∧ (p5 ∧ p4)) ∧ ((p2 ∧ (p4 → p2)) ∨ ((p3 ∨ p4) → False))) ∨ (True → (((p2 → (p4 ∧ p3)) ∧ p4) → (p4 ∨ p3)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232014363329913267695492827748 : (((p2 ∨ p5) → p3) → ((p4 ∧ ((p5 ∧ ((False ∨ p4) → (False ∧ p4))) ∧ (((p4 ∧ False) → p2) → p3))) → (((p3 ∧ p1) ∨ p3) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : (False ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h2.left
  let h13 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h13.left
  let h15 := h13.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
  have h18 : (False ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h17, we can now drive its conclusion.
  let h19 := h17 h18
  -- We need to get the left conjuct of h19 based on <expert-advice>.
  let h20 := h19.left
  -- False on the left can always be used.
  apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1711651908685512503736929089 : (((((p5 ∨ (((p2 ∧ p4) → ((p2 → p1) ∨ (p3 → p5))) → p4)) ∨ (p4 → p4)) ∧ True) ∨ (p1 ∧ p1)) ∧ ((True ∨ True) ∨ p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_36379257095007278015553016748 : ((p4 → (((((p4 → ((p5 ∨ p4) → ((p5 → p1) ∧ (p5 → p4)))) → p2) ∧ p1) ∨ p4) ∧ ((True → (False ∨ (p3 ∨ True))) ∧ p4))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350011870637077092182247770539 : (p4 → (((p3 → ((p2 ∧ (p2 → ((p3 ∨ p2) ∧ (((p3 ∧ (p2 ∧ p2)) → (p5 ∨ (p5 → p2))) → (False ∨ p1))))) ∨ True)) ∨ p5) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726054953060482639718799780063 : (((((False ∧ False) ∨ p1) ∨ (((((p2 ∨ p4) ∨ p5) ∧ (((p4 ∨ p1) → p2) ∧ (p5 ∨ (p2 ∧ (False ∧ p1))))) ∨ p1) ∨ (p1 ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262277734175652193322745354759 : (True ∧ ((((p1 ∧ (True → ((p3 ∧ p4) → p2))) ∧ (((p5 ∨ (p1 ∨ (p1 ∧ p3))) ∨ p5) → p4)) → ((p5 ∨ (p4 → p2)) ∧ p3)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593210311562330682028272533839 : ((((((p2 ∨ p2) → ((((p4 ∧ (True → (((p5 ∧ p3) ∧ p2) ∨ p5))) ∨ p3) → False) ∧ (p5 ∨ p4))) ∨ (p1 ∨ (p3 → p2))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159593330243355904378229669028 : (((p4 → ((False ∧ ((p4 ∧ ((True ∧ False) → p1)) ∨ ((True → (p2 ∧ p4)) → p1))) ∧ True)) ∧ p2) → (((p4 → False) ∧ (True → p4)) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h7
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h9 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h9
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327845791273061688563140483265 : (True → ((((p4 ∨ ((False ∨ p1) ∨ p4)) ∨ ((p1 ∧ p5) → False)) ∧ ((True → (p2 ∧ (p5 ∧ False))) ∧ ((False ∨ p5) → True))) ∨ (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169619503419196612129583208097 : ((((((p2 → ((p1 ∨ p2) ∧ p2)) ∨ (False → p1)) ∨ (p3 → False)) → False) → p3) ∧ ((((p1 ∧ p4) ∨ p3) ∧ True) ∨ (p5 → (True ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 → ((p1 ∨ p2) ∧ p2)) ∨ (False → p1)) ∨ (p3 → False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639698528831921012281212733943 : (((((p4 ∨ (True → p1)) ∧ ((True ∨ ((((True ∨ p2) ∨ True) ∧ p3) ∧ ((p3 → p5) ∧ (p1 → p5)))) → ((False → p2) → p1))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58546359416984993401683279794 : (((p5 ∨ p5) ∧ (((p4 → (True ∧ (p4 ∧ (((p5 → (p4 ∧ (True ∨ p5))) ∨ p1) ∧ (p1 ∨ p3))))) ∧ ((p1 ∨ p4) ∨ p4)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196715367605174403079168701251 : (((((p4 → (False ∨ p5)) ∨ p3) → p4) ∧ p3) ∨ (False → (((False → (((p2 ∧ (p3 → (p5 ∨ p1))) → p4) ∧ p4)) → (False ∨ p2)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136357202355311492762055116919 : (((((True ∧ p3) ∨ p4) ∧ p5) ∨ (p2 ∨ ((((p2 ∧ False) ∨ (p3 ∧ (True ∧ p1))) ∧ (p2 ∨ p2)) → (p2 ∧ p5)))) ∨ ((p4 → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318573220403874107520031527645 : (p4 ∨ (((p3 ∨ ((((p2 ∨ ((p4 ∧ p4) ∧ False)) ∨ (True → p4)) → (p2 ∨ ((p5 ∨ (p4 ∨ p2)) → p2))) → p3)) → p4) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598093215903048195298143365036 : (((((p5 → (p4 ∧ p5)) ∧ (p1 → (True → ((False ∧ p1) ∨ ((p1 ∨ p3) ∧ ((((p2 ∨ p3) ∧ (p4 ∧ p4)) ∨ p1) ∧ p4)))))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636023095756240722026125525974 : ((((((p2 ∧ (p5 → p1)) ∧ ((True → ((True ∧ (p4 ∧ (p2 ∨ p2))) → p2)) → True)) ∧ (((False ∨ False) → (p4 ∧ p5)) → p4)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49967342658589121901131639678 : ((((p4 → ((p3 ∨ ((True ∨ p5) → (p1 → p1))) ∨ (p1 → (False → p3)))) ∧ ((p1 ∨ p2) → p2)) ∧ ((p3 ∨ p3) ∧ (p1 → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134487057333542867047711120756 : (((((p2 ∨ ((True ∨ (p3 ∧ (True ∧ (((True ∧ False) ∧ True) → (p3 → p3))))) ∨ (p3 → p1))) ∨ p5) ∨ p2) → p3) ∨ ((p1 → p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340872848998298969122143699630 : (p2 → (((((p3 ∧ (False → True)) → (((p5 ∧ p5) ∧ False) ∧ (p1 → True))) ∧ (p2 ∧ p2)) ∧ ((p4 → (p4 → (p1 → p2))) ∨ False)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41993354230931641966766725464 : ((((True → p3) ∧ (False ∨ (((p2 ∨ p4) ∧ p2) → (False ∨ ((True → False) ∧ (p2 ∧ (p1 → (p3 → ((p4 ∧ p3) → p4))))))))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_407847604137301082961205379639 : ((((((p3 ∨ ((p3 ∨ (((p1 → (False ∨ (p5 ∧ p2))) ∨ p4) ∨ ((False ∨ p4) ∨ p1))) ∧ p4)) ∧ p2) ∧ (p2 → (p2 ∧ False))) → p5) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h14 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h15 := h3 h14
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h20 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h5
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h21 := h3 h20
          -- We need to get the right conjuct of h21 based on <expert-advice>.
          let h22 := h21.right
          -- False on the left can always be used.
          apply False.elim h22
        case inr h23 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h24 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h5
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h25 := h3 h24
          -- We need to get the right conjuct of h25 based on <expert-advice>.
          let h26 := h25.right
          -- False on the left can always be used.
          apply False.elim h26
      case inr h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- Disjunctions on the left can always be decomposed.
          cases h28
          case inl h29 =>
            -- False on the left can always be used.
            apply False.elim h29
          case inr h30 =>
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h31 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h5
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h32 := h3 h31
            -- We need to get the right conjuct of h32 based on <expert-advice>.
            let h33 := h32.right
            -- False on the left can always be used.
            apply False.elim h33
        case inr h34 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h35 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h5
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h36 := h3 h35
          -- We need to get the right conjuct of h36 based on <expert-advice>.
          let h37 := h36.right
          -- False on the left can always be used.
          apply False.elim h37
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69086690132766549256990978316 : ((p5 → (((p4 ∨ True) ∧ ((((((p5 ∧ p3) → (p3 ∨ p3)) → False) ∨ p3) → ((p1 → p4) → p5)) ∨ ((p3 ∨ p2) ∧ True))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_387530184615950461652736354745 : (((((p2 ∧ (((True → (p4 ∨ p4)) ∧ p4) ∧ ((p1 ∧ (p3 ∨ p1)) → ((False ∨ (p5 ∧ p4)) → p2)))) ∨ ((p5 ∨ False) → p3)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_164573799055239432721847599737 : (((((p5 ∨ p2) ∨ p3) ∨ ((p2 → ((p3 ∨ False) → ((True ∧ p1) ∨ p4))) → p5)) ∧ p2) ∨ (p1 ∨ (False → (((False ∧ p5) ∧ False) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117557119470841284920451206105 : ((p2 ∧ ((((p5 ∨ (p1 ∧ (True ∧ p2))) → (p1 ∨ False)) ∧ p4) → ((p2 → p5) → ((p1 → p5) → ((p4 ∨ p1) ∧ False))))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662774580397091365934186138165 : (((((p3 ∧ ((p2 ∨ p3) ∨ False)) → ((p5 → ((((True ∧ True) → False) → (((p1 ∨ p3) ∧ p3) → p5)) ∧ p4)) ∨ True)) → (True ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64664593180782744616410049722 : ((p1 ∨ (p1 ∨ ((True → ((p2 ∨ ((True ∨ False) → (p1 ∨ p2))) ∧ ((p3 → ((((p3 → True) → p1) ∨ p5) → p3)) → p2))) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_517086674542001307916764088 : (((p2 ∧ (p5 → ((((p5 → (True ∧ ((p2 ∨ True) → p1))) → (False ∨ (False ∨ p5))) → (False ∨ p3)) ∨ (False → True)))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197582476883012805182258915122 : (((False ∧ (p3 ∨ (False ∧ False))) ∨ (p5 ∧ p2)) ∨ (((((p1 → p5) ∧ (p5 → (((False ∨ p2) ∧ p4) → p3))) → False) ∨ p1) → (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_951425920575754300836604949364 : ((((p5 ∨ (False ∨ True)) ∧ (((((((p3 ∨ p4) → (True ∧ ((p4 ∨ (p5 ∧ p1)) ∧ False))) ∨ p4) ∨ False) ∧ (p5 ∨ True)) ∨ True) → False)) → p5) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h8 : ((((((p3 ∨ p4) → (True ∧ ((p4 ∨ (p5 ∧ p1)) ∧ False))) ∨ p4) ∨ False) ∧ (p5 ∨ True)) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h9 := h3 h8
      -- False on the left can always be used.
      apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3936704503653392595021717972 : (False ∨ ((p3 ∨ p4) ∨ (p5 ∨ (True ∧ (p4 ∨ (False ∨ ((False → p2) ∨ (p3 ∨ (((p4 → False) ∧ False) ∧ (p1 ∧ (p2 ∧ p4))))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603049595347459310086980851327 : ((((p1 ∨ (p3 ∨ (((False ∧ ((True ∧ False) ∨ p2)) ∨ p5) ∨ ((p3 ∨ ((p4 ∨ p2) ∧ p2)) → (((True ∧ p3) → False) ∧ p5))))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344209384374877219652426542091 : (p2 → (p1 ∨ (p1 ∨ ((True → False) → ((False ∧ (False ∧ (False ∧ (p5 ∧ p1)))) ∨ ((p2 ∨ (p1 ∨ (((False → True) ∧ True) → p2))) → p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343124766178784394742666990270 : (p2 → (((True ∧ False) ∧ p3) ∨ (((p2 ∨ ((p3 ∧ ((p2 ∧ p3) ∨ (False ∧ False))) → p3)) ∨ p2) → ((p4 → (p1 → (p3 ∨ p1))) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116480891575410548153730788583 : (((p1 ∧ p5) ∧ ((p5 ∨ ((p3 → (p1 → (p2 ∧ True))) ∨ (((p5 ∧ (True ∧ p3)) ∨ ((False ∨ True) → p4)) ∧ p1))) → p4)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653626363107743984206683462965 : (((((((p4 ∧ (p4 ∧ ((False ∧ p4) ∨ (((True ∨ (p1 ∨ p4)) → p5) ∨ (p5 ∧ (True ∧ p4)))))) → p2) ∨ p3) ∧ True) ∨ (p4 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309720806655192257450041044821 : (p2 ∨ ((p2 ∨ ((False → (p1 ∧ p1)) ∧ (((p4 ∧ p4) ∧ False) → (p1 → (True → (((p2 → p2) ∨ p4) ∨ p1)))))) → ((p1 ∨ False) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358155885671143505359724214240 : (p5 → (p3 ∨ (((((False ∨ ((False ∨ False) → (p4 ∨ (True ∨ p3)))) ∨ p1) ∧ (False ∨ (p4 → (p3 ∧ (p2 ∨ p2))))) → (p4 → False)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252602288856237893257746781258 : ((p5 → p3) ∨ ((p5 ∨ True) ∧ (((((((p4 ∨ p2) ∧ p3) → (p5 ∨ ((p3 ∧ p5) ∨ True))) → p2) → ((p1 → p2) → p4)) → p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655337010782916124108902252377 : ((((((((False ∨ p5) ∧ (((False ∧ p2) → (True ∨ p2)) ∧ (False ∧ ((p5 → p4) ∧ False)))) ∨ p3) ∧ p5) ∨ (False → False)) ∨ (True ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_205515782454464178883016880355 : (((p5 ∧ p2) ∧ (p5 ∧ (p4 ∨ p4))) ∨ (((True ∧ False) ∧ p4) → (((((p5 ∨ p3) → (p5 → p2)) ∧ p5) ∧ p2) → ((p1 ∨ p3) ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h2.left
  let h12 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h11.left
  let h14 := h11.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h1.left
  let h16 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h17 := h15.left
  let h18 := h15.right
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241325978286551822488081363321 : ((False → True) ∧ (p4 → (((p5 → (((p2 ∧ p3) → False) → (True ∧ p5))) → False) ∨ (((p3 ∧ ((p2 ∧ p3) ∧ (p3 → p4))) → p4) ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304693319354701170598819630631 : (p1 ∨ (((p5 ∨ (((((((False → (True ∧ p1)) ∨ p3) → p1) ∧ (True ∧ True)) ∨ ((p3 ∨ True) → p1)) ∧ p1) ∧ p5)) ∨ p5) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157262668112389857691773551675 : ((((((True ∨ p3) → p3) → p3) → ((p5 ∨ ((p2 ∧ p5) → ((p2 → p5) → False))) → p3)) → False) ∨ (((True ∧ p5) → False) → (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806182475839435845607608988081 : (((p4 → (((True ∧ (((((p2 ∧ (p1 → True)) → (p1 → (((True ∧ p5) → p4) → (p4 ∨ p5)))) → p5) ∨ p1) ∨ p2)) ∨ True) ∨ p2)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736088461985722490578495731708 : ((((True → p5) ∧ (p2 ∧ ((((p1 → p2) ∧ True) → (p1 ∧ ((((False ∧ p5) ∧ (p2 ∧ p1)) ∨ p2) ∧ (p3 ∨ (p5 ∨ p5))))) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40874304900064302693473016037 : (((((((((p5 → p4) ∨ p4) → ((p2 ∨ ((p3 → True) ∨ True)) → False)) → (p3 ∧ p3)) ∧ p3) → (p3 ∧ p2)) ∧ (p4 → p4)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174861789634564217858386070713 : (((p5 ∨ p3) ∨ (p5 ∧ (((True → (False ∨ p3)) ∧ (p5 ∨ False)) ∨ (p3 ∨ p2)))) → ((True ∧ ((False → False) ∧ p5)) → (p4 ∨ (p4 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180678107554556821002956268267 : (((((True → False) ∧ False) → (p2 ∧ p2)) → (((p2 → p3) ∧ p5) → p1)) → (p2 ∨ ((p1 ∧ False) ∨ (((p5 ∧ (True ∧ p3)) ∨ False) ∨ True)))) := by
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
theorem thm_5_vars_310250806785110477055882375245 : (p2 ∨ ((p4 ∧ (((p4 ∨ False) ∧ ((p1 ∧ p1) ∨ p3)) ∨ (p1 ∧ p4))) → ((False ∨ (((p3 ∨ (p3 ∨ p4)) → (p4 → p3)) ∨ p1)) ∨ p2))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h12
        -- Implications on the right can always be decomposed.
        intro h13
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h14 =>
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- One of the premise coincides with the conclusion.
            exact h16
          case inr h17 =>
            -- One of the premise coincides with the conclusion.
            exact h11
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41709131265480655883047988749 : ((((True ∨ (((p1 → p3) ∨ p3) ∧ p4)) → ((((True ∧ (p1 ∧ (((p2 ∨ (p2 → p3)) ∨ p4) ∨ False))) ∧ False) → True) → p4)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111261381070571892609647165382 : ((((p5 ∨ p2) ∨ (((((True ∧ ((p2 ∨ p4) → (p4 → p4))) ∧ False) → ((True ∨ True) → p3)) → False) ∨ (p1 → p5))) ∧ True) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253034926147385088809572376665 : ((True ∧ p3) → (p3 ∧ ((p3 ∨ p2) → (((((True → (p5 ∨ False)) → p5) ∧ True) → (p4 ∨ (False ∧ p2))) ∨ ((True ∨ (p4 ∨ p5)) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50397718479530081455480942290 : ((((p2 ∨ p1) → ((((((True ∨ p2) ∧ p2) → p5) → p3) → ((True → (p1 ∨ p4)) ∧ p4)) ∧ True)) ∨ (False → ((p2 → True) ∧ False))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190063963641970801655507648588 : (((((True ∧ ((p2 ∨ p1) ∧ True)) → p3) → True) ∧ p1) ∨ (p4 ∨ ((((p5 ∨ (p4 ∨ p2)) → p4) ∧ p1) → (p3 ∨ ((p2 → p1) ∨ True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323358020297951943859745778940 : (p5 ∨ (((p3 ∨ (True → p3)) → ((p2 ∨ (p3 ∨ (((((p3 ∧ p2) → (p5 ∧ p5)) ∧ (p4 ∨ p5)) ∧ p5) → True))) → p1)) → (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596342957796378701151989146793 : ((((((True ∧ ((p2 ∨ (p1 → p4)) → p5)) → p2) ∨ ((True → (True ∧ ((p4 → False) ∨ p2))) ∧ ((p5 → p4) ∧ (p3 ∨ True)))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205625534885438385640433985848 : (((p2 ∧ True) ∨ (p5 → (False ∨ p2))) ∨ ((p2 ∧ (p4 ∧ (p5 ∨ p3))) ∨ (p2 ∨ ((False ∨ (p1 ∧ p1)) ∨ (True ∨ (p1 → (True ∨ p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_651451607422251222352969969885 : (((((p4 ∧ (False ∨ p3)) → (True ∧ ((p5 ∨ ((True ∧ ((p5 ∧ False) ∧ (False ∨ p5))) ∨ (p1 ∨ (p3 → True)))) ∨ p2))) ∧ (False → True)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198014714623508570689334630473 : (((p3 → True) ∧ (((p3 ∨ False) → p3) → False)) ∨ ((False ∧ ((p1 ∨ (p5 ∨ p5)) ∧ False)) ∨ ((True → p1) ∨ ((p4 ∧ p4) → (p4 ∨ p2))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320020871221239641873646769019 : (p4 ∨ (((True ∧ p4) ∨ p5) ∨ ((p1 → ((((((p5 ∨ p5) → (p5 ∧ (True ∧ p5))) → (True ∧ p2)) ∨ False) ∨ p3) ∨ True)) ∨ (p4 ∨ False)))) := by
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
theorem thm_5_vars_55921081222143314115925123704 : (((False → ((True ∧ True) ∨ p1)) ∧ ((p5 → p3) ∨ ((p1 ∨ ((True ∧ p4) ∧ False)) ∧ (((p1 → True) ∧ (p5 ∨ p5)) → (p3 → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147438869650734756672805156443 : ((((p2 ∨ False) ∧ (p4 ∨ (((p1 ∨ (True → p1)) ∨ ((p5 ∧ True) → False)) → ((p1 → False) → False)))) ∨ p5) ∨ (p2 → (False → (p5 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_31565115424803975609963406710 : ((False ∨ ((((p3 ∧ p4) → (p3 ∧ (((p2 ∨ False) → p4) → (p2 ∧ ((((True ∨ True) → (p4 ∧ p3)) ∧ False) ∧ p4))))) ∨ p4) ∨ True)) ∧ True) := by
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
theorem thm_5_vars_57811988348510922018197809461 : (((p2 ∧ (p4 → p1)) → (p2 ∧ (((True → ((p4 → (p1 ∨ (((True ∧ True) → p4) ∧ p3))) → p4)) ∧ (p1 → (p3 ∧ False))) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113506303007411912071895390774 : (((((False ∨ p2) ∧ (((((p5 ∨ True) ∧ p2) ∧ p5) ∨ p1) ∨ (p4 → False))) ∨ (p4 ∨ (True ∨ (p3 ∨ p5)))) ∨ (p1 ∧ p1)) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748934114374442232478247981717 : ((((p4 → p3) → (((p4 ∨ (p3 → ((p2 ∨ (((p5 → (False ∨ ((p5 ∧ p2) ∨ p1))) → False) → p1)) → (p3 → p2)))) ∨ True) ∨ p3)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49491314551008230645179663088 : (((((p4 ∨ ((p1 → p3) ∨ False)) → ((p1 ∧ (p2 ∨ (True → ((p3 ∨ (p4 ∧ p1)) → True)))) ∨ False)) → True) → ((p3 ∧ p1) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58731892388821794662495010609 : (((p3 → p3) ∧ ((((False ∧ ((p3 ∨ (p5 ∧ p4)) ∧ (p2 ∧ (p1 ∨ False)))) ∨ (True ∧ (p5 ∨ (p2 → p1)))) ∨ (p4 → True)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180910221783272406310268133970 : (((True → (p2 ∧ p1)) → ((((p2 ∧ True) ∨ (False ∧ p3)) ∧ p1) ∨ p4)) → ((p1 ∧ (False → ((False → ((False ∨ p3) → p4)) → p4))) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302621714382430207856972941760 : (False ∨ (p2 ∨ ((p5 ∨ (((p5 ∧ p5) ∨ ((True → p1) → False)) ∨ (((p3 → p5) ∨ ((p5 ∧ p2) → (p4 → (True ∨ p5)))) → p2))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798536510533264894577837568771 : (((p1 → ((((((p1 → p1) → p1) ∨ True) → p3) → p1) → ((False ∨ (p2 ∧ (p5 ∧ (p4 ∧ ((p1 ∨ (p2 ∨ p1)) → p2))))) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52441296434280435801655307079 : (((False ∧ ((p3 ∨ False) ∨ (p5 ∨ ((p2 → p5) ∨ ((p2 ∧ p3) ∨ p4))))) ∧ ((True ∧ p3) ∧ ((True → (p5 → (p5 ∨ p3))) → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617156398136344549672811256159 : ((((((p1 ∧ (((p1 ∨ p2) ∧ p4) ∧ p4)) ∨ False) ∨ (p5 ∨ (p4 → (((True → p1) ∨ (False ∨ False)) → (p1 ∧ (p1 ∨ p5)))))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323468704594489293431552768680 : (p5 ∨ ((((p2 → (p1 ∨ (True → ((p3 → (((p3 ∨ (p1 ∨ (p5 → True))) → False) ∨ p4)) → False)))) → p4) ∧ p4) ∨ (p5 → (p4 → p4)))) := by
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
theorem thm_5_vars_254149986795180848548381148757 : ((p2 ∧ p1) → (((p3 ∨ (p5 ∧ (p2 → p3))) ∧ ((False ∧ (((p3 ∨ (p5 ∨ (p3 ∧ (True → (p4 ∨ p4))))) → False) ∧ True)) ∨ p2)) ∨ p1)) := by
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
theorem thm_5_vars_53131806123705759970187674216 : ((((((((p3 ∨ p3) → p3) ∧ False) → p5) ∨ (True ∧ p5)) ∧ False) ∨ (False ∨ (p2 → (((p1 ∧ (False ∨ p5)) → False) → (p2 → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139445823508919440594460983643 : ((((((True ∧ p3) ∨ (((p2 → ((p5 → p2) ∨ True)) → (True → ((p5 ∨ p2) ∧ p1))) ∨ True)) ∨ p3) ∨ p1) → p3) → (True ∧ (True ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((True ∧ p3) ∨ (((p2 → ((p5 → p2) ∨ True)) → (True → ((p5 ∨ p2) ∧ p1))) ∨ True)) ∨ p3) ∨ p1) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178197362128063441096848938349 : (((True ∨ (((((p1 → p3) ∨ p5) ∨ p4) → (p2 ∨ False)) ∨ True)) → p1) ∨ ((((True ∨ p2) ∨ (p3 → (p3 ∨ True))) ∨ False) → (True ∨ p3))) := by
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118607023093312899573794430575 : ((p4 ∨ (((((False ∨ p1) ∧ True) → (((p4 ∧ True) → (False ∨ p5)) ∧ p4)) ∨ ((False ∧ True) ∨ p1)) → (p4 ∧ (p4 ∧ p5)))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254756447914871230766056344913 : ((p3 ∧ p4) → (((p1 ∧ ((p2 ∨ (p2 ∧ (((True → p2) ∧ ((False ∧ p2) → p2)) ∨ p2))) ∧ p2)) ∨ ((p1 ∨ (p2 ∧ False)) ∧ p2)) ∨ p4)) := by
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
theorem thm_5_vars_40809531485032754811598797744 : ((((p2 ∨ ((p5 → (p4 ∨ (False ∨ ((False → True) ∧ ((True ∧ p1) ∨ p2))))) ∧ ((p2 ∨ p1) → (p4 → (p1 ∧ p4))))) → False) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



