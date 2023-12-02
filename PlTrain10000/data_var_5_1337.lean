variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349034889842573910165199633477 : (p3 → (p5 ∨ ((p5 → ((((p2 ∧ (((p4 ∨ False) → False) ∨ (p5 → ((False ∧ p3) → p3)))) ∧ p5) → p5) → ((True → False) ∨ True))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595851963205343360442319985179 : (((((((p1 ∨ (p3 ∨ (p3 ∨ (p1 → p3)))) → True) ∧ p4) ∨ ((True ∨ p1) → (p1 ∧ (False ∨ (p2 ∨ ((False → p1) ∨ p2)))))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41333492753015533057352058566 : (((((False ∧ ((p4 → True) ∧ (((p5 → p4) ∨ (p5 ∧ (p1 ∨ p5))) ∧ p1))) ∨ True) ∨ ((p1 ∧ (p5 ∧ p3)) → (p4 ∨ p4))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618343922525974850049375735022 : (((((p5 ∧ ((p2 ∧ False) ∨ p2)) ∨ (((p1 ∧ p1) → ((p5 → p5) ∨ (((False ∧ False) ∧ True) ∧ p3))) ∧ ((p3 ∨ p5) ∨ False))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122143561835773572118922303702 : ((((p3 ∨ ((((p3 → p4) → False) ∧ ((((p1 ∨ (True ∨ p5)) ∧ (p5 ∧ p5)) ∨ p1) → True)) ∧ p4)) ∨ False) ∧ (False → False)) → (p3 ∨ p1)) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h11 : (p3 → p4) := by
        -- Implications on the right can always be decomposed.
        intro h12
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h13 := h9 h11
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662095040928544569391382228843 : ((((((((p3 ∧ True) → p3) → ((p4 ∨ p2) ∨ p3)) ∧ (p5 ∨ True)) ∨ (p5 ∧ (False ∧ (p2 ∨ ((p1 ∧ p1) ∧ p2))))) → (p1 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249427505110340971685196864926 : ((p5 ∨ False) ∨ ((p4 ∨ (p1 ∧ ((False → (p2 ∧ (p3 ∧ p1))) ∨ (p4 → (p3 → (False ∨ ((p5 → True) → False))))))) ∨ ((True → False) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_199854301416411746892077600585 : (((True ∨ (True ∨ (False → p3))) ∧ (p1 ∧ p4)) → (((False ∨ p3) ∨ (p5 ∨ (False ∨ ((p5 → ((p2 ∨ False) → (p1 ∨ p3))) ∨ False)))) ∧ p1)) := by
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
    let h5 := h3.left
    let h6 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h3.left
      let h14 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h15
      -- Implications on the right can always be decomposed.
      intro h16
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h18 =>
        -- False on the left can always be used.
        apply False.elim h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h3.left
      let h21 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h22
      -- Implications on the right can always be decomposed.
      intro h23
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h25 =>
        -- False on the left can always be used.
        apply False.elim h25
  -- Conjunctions on the left can always be decomposed.
  let h26 := h1.left
  let h27 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h26
  case inl h28 =>
    -- Conjunctions on the left can always be decomposed.
    let h29 := h27.left
    let h30 := h27.right
    -- One of the premise coincides with the conclusion.
    exact h29
  case inr h31 =>
    -- Disjunctions on the left can always be decomposed.
    cases h31
    case inl h32 =>
      -- Conjunctions on the left can always be decomposed.
      let h33 := h27.left
      let h34 := h27.right
      -- One of the premise coincides with the conclusion.
      exact h33
    case inr h35 =>
      -- Conjunctions on the left can always be decomposed.
      let h36 := h27.left
      let h37 := h27.right
      -- One of the premise coincides with the conclusion.
      exact h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174964276505703539781362544026 : ((True ∧ ((p4 ∨ (p3 ∨ True)) ∨ (False ∨ (p1 → (p3 ∨ (p2 → (True ∧ p5))))))) → (((p1 → p3) ∨ True) ∨ (p5 → ((False ∨ True) → p1)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788646725883943697629358760463 : (((p5 ∨ ((((p5 → ((((((p1 → p1) → p1) ∧ p2) → (p2 ∨ False)) → p4) ∨ p5)) → (False ∧ (p5 ∨ p1))) ∨ (p2 ∧ p3)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44868719953712068272434748158 : ((((p3 → (p5 ∧ True)) ∨ ((p5 ∨ False) ∨ (p5 ∨ ((True → ((True ∧ (((p2 ∨ p5) ∨ p1) ∧ (p4 ∧ False))) ∧ p1)) → p3)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149703191088637706095020229859 : ((p5 ∧ ((p2 ∨ p1) ∨ (((p5 ∧ (p2 ∧ ((False ∨ True) → (p4 ∨ False)))) → ((p1 → True) ∨ p3)) → p2))) ∨ ((p3 ∨ True) ∨ (p4 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655032413986595573541656328929 : (((((True ∧ ((((True ∨ (p4 → p4)) → (((False ∨ (p2 ∧ p5)) → p3) ∨ p1)) ∨ p3) → ((p3 ∧ p5) → False))) → False) ∨ (False → p3)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_158441503796000361643438962526 : (((p2 ∨ p5) ∨ ((((False ∧ False) ∨ p2) ∧ (False → ((p2 ∨ ((p5 → p5) → p5)) ∧ p1))) ∨ p1)) ∨ (True ∨ (p1 → ((p1 ∨ False) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308372992577573066066709682614 : (p2 ∨ ((((p1 ∧ ((True → ((((False ∨ (p2 → ((p4 → False) ∧ False))) ∧ (p4 ∧ (p4 ∧ p5))) ∨ True) ∧ p4)) → p4)) ∨ p3) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58226306532337479852589810474 : (((p4 ∧ p4) ∧ (((p5 ∧ (p1 ∨ ((p4 → p5) → (((p4 ∨ p5) ∨ True) → ((p3 ∧ ((p2 → p1) ∨ p5)) ∧ p3))))) → True) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192570333704332546169282580633 : (((p4 ∨ ((((p2 → p1) ∨ False) ∧ p1) ∨ True)) ∨ p1) → (p5 ∨ (p1 → ((((((p3 → p2) ∧ p4) ∨ False) → p1) → (True ∧ p2)) ∨ p1)))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h10
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h11 =>
          -- False on the left can always be used.
          apply False.elim h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59685457139535681184530934246 : (((True ∧ p4) → ((True ∨ False) → ((((p3 ∧ p3) → p4) ∧ (p4 ∧ (p3 ∧ (p1 ∨ False)))) ∨ (((True → p1) → p2) → (p2 ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179815383119946741099522326375 : (((True ∧ ((p3 → ((p5 ∧ p2) ∧ (p3 ∧ p4))) → (p1 ∧ p1))) ∧ p1) → ((True ∨ ((p4 → p4) ∨ False)) ∧ ((p3 → (p1 ∧ p2)) ∨ p1))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142958312373265043489503191537 : ((p5 ∨ (p4 ∨ ((False ∨ ((p5 ∨ ((True → p2) → (p2 ∧ (p1 ∨ False)))) ∨ (((p4 → p1) → False) ∨ True))) ∧ p3))) → (p1 → (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
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
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51273220714427089831471557828 : (((True ∧ (p5 ∧ ((p4 ∨ p4) ∨ ((((p4 → (p4 ∧ False)) ∧ p2) ∧ (p5 ∨ p1)) ∧ p3)))) ∨ (((False ∧ (p4 ∨ p5)) → False) ∨ p1)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204876896445705822245668212851 : ((((p3 ∨ (p1 → p1)) → p3) → p2) ∨ ((p3 ∨ (((p1 ∧ p5) ∧ (((p3 ∨ p4) ∨ p4) ∧ p3)) ∨ ((p4 ∧ p1) → (p4 → p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172561917151755590913550051522 : (((p4 ∧ (True ∧ False)) ∨ (((((p5 ∨ True) ∨ (p3 → p1)) ∨ p2) → True) → p1)) ∨ ((p4 ∨ ((p1 ∨ (p1 → (p3 ∨ p3))) ∧ p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190674193771078625772790147760 : (((p2 → (((p5 ∨ False) ∨ True) ∧ (True ∧ p3))) → p5) ∨ (((False → p1) ∧ (p4 ∧ p1)) → (((p5 ∨ False) ∧ ((p4 → p4) ∨ False)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321768089555298308272776431838 : (p4 ∨ (p5 → (p2 → ((p5 ∧ (((True → (p3 ∨ ((((((True → p4) → p1) ∨ True) → (p1 ∧ p2)) ∨ False) → p4))) ∨ p2) ∨ True)) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144531309678978713638331279592 : (((((((p4 → (p3 ∧ ((p3 ∧ p4) ∨ (False → p5)))) ∨ False) ∧ p5) → p3) ∧ (p3 ∧ p5)) ∨ (p3 ∨ True)) ∧ ((p4 → p4) ∧ (True → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157839083916360288198400242290 : ((((((p5 ∨ True) ∨ p5) → ((p3 → True) → p1)) ∧ p2) ∧ ((p2 ∨ (True ∧ p1)) ∨ (p1 ∧ False))) ∨ (((False ∧ (False ∧ True)) → True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174006151564088013629680567435 : (((False ∧ ((p5 ∨ (p2 ∨ (p2 → p4))) ∨ (False → (True ∨ (p5 → p2))))) → p1) → ((p1 ∨ p5) → ((p4 ∨ (False ∨ p4)) ∨ (True ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114428126371449124751897727259 : (((p3 ∧ ((p1 ∧ ((p2 → p3) ∨ p5)) ∨ ((((p3 → p4) ∧ p3) ∨ (True ∧ p3)) ∧ p3))) ∨ (p1 ∨ ((p1 ∨ p1) ∧ p5))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8866483431118909953678732334 : ((((((False ∨ p3) ∨ (False ∨ p3)) ∨ (p3 ∨ ((((p4 ∧ p1) ∧ True) ∧ p4) ∨ (p4 → p4)))) ∧ ((p4 → p3) ∨ (True → True))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52013585322224611625117145711 : (((p4 ∧ (p2 ∧ ((p2 ∨ ((p4 ∨ ((p1 ∧ p2) ∨ (p4 ∧ True))) ∨ True)) ∧ p4))) ∨ (p1 → (p4 → (p5 → ((p1 ∧ False) ∨ p4))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619768786443894745751538833360 : (((((False ∨ p5) ∧ ((p4 → (((p4 ∨ p1) ∨ (p1 → True)) ∧ (p2 → p2))) → (p2 ∧ ((True ∨ p1) ∨ (False ∧ (p4 → p4)))))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_165028852677133812272007711868 : (((((p3 ∨ p5) → False) ∨ (p1 → (((False ∧ p2) ∧ (True ∨ (p4 ∧ p3))) ∨ p3))) → False) ∨ (p1 ∨ (((p2 → p3) ∨ (p3 ∨ False)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308444667454920051854855982065 : (p2 ∨ (((p4 → (p5 ∧ ((True ∧ (True → (p3 → (p5 ∧ p2)))) → (p1 → ((((p4 → p3) ∧ (p1 → True)) → p5) ∨ p1))))) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173308240832359995782587950947 : ((p1 → (p5 ∧ ((p5 ∨ (p4 → ((p4 ∨ (p2 ∨ p2)) → (True ∨ p4)))) → p3))) ∨ (((((p3 ∧ False) → (p4 → p1)) ∧ False) → p2) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81159361382093088393850865997 : (((p1 ∧ ((p3 ∨ (((p3 ∨ p4) ∧ ((((p2 → p3) ∧ p1) ∧ p5) → (p5 ∨ False))) ∧ (p5 ∨ p5))) ∧ p4)) ∧ (p1 → (p2 ∧ p3))) → p3) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h18 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h19 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h4
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h20 := h3 h19
        -- We need to get the right conjuct of h20 based on <expert-advice>.
        let h21 := h20.right
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h22 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h23 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h4
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h24 := h3 h23
        -- We need to get the right conjuct of h24 based on <expert-advice>.
        let h25 := h24.right
        -- One of the premise coincides with the conclusion.
        exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351844052408127923800012505619 : (p4 → (((True ∨ ((((p3 ∨ p1) ∨ (True → p1)) ∨ True) → p1)) → False) → ((p4 ∨ p2) → (((True ∨ p3) ∧ False) ∨ ((p3 ∨ False) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37260963129020419584638354589 : ((((p3 ∧ ((False ∨ ((p5 → p4) ∨ (p2 → p3))) ∧ ((p1 ∨ ((p3 ∨ (p1 → True)) → p3)) → (p2 ∧ (p3 → False))))) ∧ p1) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165039838848925590457114089785 : ((((True → False) ∧ (((True → (False → False)) ∨ (p3 → p5)) ∨ (p3 ∧ (p3 ∧ p2)))) → False) ∨ (p5 → ((False → (p1 ∧ (True → p4))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142500670929225189203111218401 : ((p5 ∧ (p2 → (p4 → ((False → p2) → ((((p1 → p3) → (True ∨ p5)) → False) → ((p5 ∧ (p2 ∨ p3)) → p5)))))) → (p1 ∨ (p3 ∨ True))) := by
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
theorem thm_5_vars_757544331747100585164776211318 : (((p1 ∧ (p2 ∧ ((((p5 → p2) ∧ p5) ∧ ((((p3 ∨ (p3 → p1)) ∧ (p1 ∧ (p4 → p3))) → p2) → ((p4 ∨ p1) ∨ True))) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115283131525407367082041220637 : (((p3 → (((True → p3) ∨ p3) → ((p2 ∧ False) ∨ p1))) ∨ ((((True ∨ p4) ∨ (True ∨ (p3 ∧ p4))) ∧ p1) → (p2 → True))) ∨ (True ∧ p1)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702376952035144035021556292591 : ((((((p3 → (((p2 → p1) ∧ p2) ∧ p2)) → p5) ∨ p3) ∨ (p3 ∧ ((True ∧ ((p2 ∧ p4) ∨ p5)) → (p1 ∨ ((p2 ∧ p4) → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212190718795859994861271023524 : ((True ∨ (p2 ∨ (True ∧ p4))) ∧ (p1 ∨ ((((p2 → False) ∨ p1) ∨ (True → ((p4 → (p2 ∨ p4)) → (p3 ∨ False)))) ∨ (False → (False ∧ p2))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251618071843956443641187674504 : ((p3 → p1) ∨ ((True ∧ (p5 → ((True ∧ ((p2 → (p5 ∨ ((p4 ∨ p4) → p2))) ∨ p1)) → p2))) → (((p4 → p1) → p1) → (p1 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768938874529690755655293092144 : (((p5 ∧ ((((p2 ∨ p4) ∨ False) ∨ p5) → ((p2 ∧ (p3 ∧ (((True → p1) ∧ p2) ∧ p1))) → ((((p2 ∧ p5) → False) ∨ True) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306032336692499601935367979847 : (p1 ∨ (((p4 ∨ (p2 ∧ p3)) ∧ True) → ((p1 ∨ p5) → (p3 ∨ (p3 ∨ (True → ((p2 ∨ (p1 → (p1 ∨ True))) → ((p5 ∨ p3) ∨ p1)))))))) := by
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
    let h4 := h1.left
    let h5 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h1.left
    let h16 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Implications on the right can always be decomposed.
      intro h19
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h21 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257766298954640262774677737761 : ((p3 ∨ p4) → ((p3 → p2) ∨ (((True → False) ∧ True) → (p2 ∧ ((p4 ∧ p2) ∨ (((p1 ∧ p5) → p3) → (p5 ∧ ((p5 ∧ p1) ∨ True)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- False on the left can always be used.
    apply False.elim h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h17 := h14 h16
    -- False on the left can always be used.
    apply False.elim h17
    -- Conjunctions on the left can always be decomposed.
    let h18 := h13.left
    let h19 := h13.right
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h20 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h21 := h18 h20
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337683654338851447975259531657 : (p1 → ((((((((p2 → p4) ∧ (p5 ∨ p5)) → ((p3 ∨ False) → False)) ∧ True) ∨ True) ∨ p2) ∧ True) → (p1 → ((p5 ∧ True) ∨ (p3 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
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
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809129583039951723022768043168 : (((p5 → ((((p4 → (p5 ∧ p3)) ∧ ((((p4 ∨ (p4 ∧ True)) → False) ∧ (p1 ∧ p2)) ∧ (((p2 ∨ p3) → p5) → p2))) ∧ True) ∨ p5)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57339469068583007884061973650 : (((p2 ∧ (False ∧ True)) ∨ ((((True → (p3 ∧ ((((p4 ∨ p4) → p5) ∧ p5) → (p1 ∧ True)))) ∧ p5) ∨ p1) → ((True ∧ p2) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51189765694535122866476379986 : (((((p1 ∨ p2) ∨ (((((False ∧ True) ∧ p1) ∨ p5) → True) → p1)) ∨ ((p2 ∨ True) ∨ True)) ∨ (False ∨ (p3 ∧ (p5 → (True ∧ p2))))) ∨ p3) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55664742367187865020008400375 : ((((p4 ∨ (p1 ∧ False)) ∧ p2) ∧ ((p5 ∧ (True ∨ (p3 ∧ (((p1 ∨ p1) ∧ ((False ∨ (p3 → p2)) ∨ (p3 → True))) ∨ p4)))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303978917668295464430944724609 : (p1 ∨ (((False ∧ p2) ∧ ((False ∧ p5) ∧ ((True ∧ ((p4 ∧ p1) ∨ ((((True → p4) → (p3 ∧ (p5 ∨ p3))) → True) → p2))) ∧ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337614271664763212321173867639 : (p1 → ((((p1 → (p2 ∧ p2)) ∨ (((p1 → ((True ∧ False) → p4)) ∨ p4) → (p2 ∨ p2))) ∨ p1) ∧ (p5 ∨ (((True → p1) ∧ p2) → p1)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640205788056347346277177384084 : ((((((p1 → p2) → True) → (((((p2 → p2) ∨ p3) ∧ p3) ∧ p2) ∧ ((p4 → (p3 ∨ p3)) ∨ ((p3 ∨ p4) → (True ∨ p4))))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168629621482973347325247465739 : ((p3 ∧ (p3 → ((p3 ∧ p3) → (((p2 → p4) → (p2 ∧ (p5 ∧ (False ∧ False)))) ∧ p4)))) → ((p1 ∧ ((True → p5) → p4)) ∨ (False ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116567248209884501227288628223 : (((p2 ∨ p4) ∧ (((p5 → (((p1 → (p5 → (p4 → p1))) ∧ (True ∨ (((p1 → p3) ∨ p1) → True))) → False)) → False) ∨ False)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158981230529986988685819861786 : ((p3 ∨ ((p5 ∨ (((True ∨ p2) → p5) ∨ (False → (False ∧ p4)))) ∧ ((p5 ∨ (p1 ∧ True)) → p1))) ∨ (((p5 ∧ (True ∨ p2)) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116679083433315071740344237000 : (((p5 → p5) ∧ ((((p1 ∨ p2) → p5) ∨ ((((False → p1) → (p5 ∧ (p2 → True))) ∧ (p2 ∧ (p2 → p5))) ∨ p3)) ∨ p1)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179413507480477417206660588442 : ((p4 ∨ ((((p1 → (True ∧ p5)) ∨ p1) → (p3 → (p4 ∧ p3))) ∨ True)) ∨ (False ∨ ((((p2 → (p2 ∨ p4)) ∨ p2) ∧ (False ∧ p4)) ∨ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201263015481295962360702171467 : ((p3 → ((p2 ∧ p2) ∨ (p1 ∨ (p3 ∧ True)))) → (((p4 → p5) ∧ (p5 ∧ ((p5 ∨ (((p2 → p1) ∨ p5) ∧ p2)) → p4))) → (p1 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_394363033453446235743270289059 : (((((p2 ∨ p3) → ((p4 ∨ ((((p2 → (False → p2)) ∨ p3) ∧ ((((p3 ∨ p4) ∨ p5) ∧ p3) ∧ p5)) ∧ False)) ∨ (True ∨ p5))) ∨ p3) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49470576853083886304710365859 : (((((((((((False ∨ p4) → p4) ∨ (p3 → (True ∧ (False ∧ p3)))) ∨ p1) ∧ False) ∨ p2) ∨ p2) ∨ p4) → p1) → (p4 ∨ (p5 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41883109200265884262911031506 : ((((False ∨ (p1 → p4)) ∨ ((p2 ∨ (p3 ∨ (((((True → ((p1 ∨ p1) → p3)) → p4) → True) → p3) ∨ (True ∨ p3)))) ∨ p2)) ∨ p3) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59686274788686769542751994158 : (((True ∧ p4) → (p1 ∨ (((False ∨ p4) ∧ p3) ∨ ((((True ∨ p2) → p3) ∨ ((True ∨ False) → (((p4 ∨ p5) ∨ p3) → p4))) ∨ False)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69380912793703097461190460823 : ((p5 → (p1 → ((((p2 → p4) ∧ (((False ∧ (((False → p3) ∧ p2) ∨ p4)) ∨ (p5 ∧ p3)) ∨ True)) → (False ∨ p3)) ∨ (p1 ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231945660147810851286111044467 : (((p1 ∨ False) → p1) → (True → (((p3 ∨ True) → (((p2 → (False ∧ (((False → (p5 → (p3 ∨ True))) ∧ p2) → p1))) → False) ∧ False)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_913179198664630930595612187565 : (((((p4 ∧ p5) → ((((p5 ∧ False) ∧ p4) ∨ ((p1 ∨ p2) ∧ ((p2 ∨ p4) ∨ p4))) ∨ True)) → ((True → p1) ∧ (p2 ∧ (p2 ∨ p2)))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∧ p5) → ((((p5 ∧ False) ∧ p4) ∨ ((p1 ∨ p2) ∧ ((p2 ∨ p4) ∨ p4))) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
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
theorem thm_5_vars_675245603338950351945179877550 : (((((p4 ∧ (False ∨ (((True ∧ p1) → p5) ∨ (((((False → p2) ∧ p4) ∨ p4) → p3) ∧ True)))) ∨ p1) ∧ (((p4 → p1) → True) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321297761158765083685950236814 : (p4 ∨ (p5 ∨ (((((((p4 ∧ (p3 ∧ ((((p5 ∨ p1) ∨ (p1 ∧ True)) ∧ p5) → p1))) → (True → p5)) → p1) → p3) ∨ True) → p2) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p4 ∧ (p3 ∧ ((((p5 ∨ p1) ∨ (p1 ∧ True)) ∧ p5) → p1))) → (True → p5)) → p1) → p3) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308099657400293047788766519812 : (p2 ∨ ((((((p5 → (False ∧ p3)) ∧ (((p3 ∧ p4) → p1) ∧ p4)) ∨ p2) ∨ True) ∨ (((False ∧ p3) ∧ True) ∨ (False ∨ (p4 → False)))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_730848406315153155894453720201 : ((((p5 ∧ (p3 ∨ True)) → (p1 ∧ (p5 ∧ (((p1 ∨ p5) → (p1 → (((p2 ∧ ((p3 → p3) ∨ (p5 → p5))) → p4) ∧ True))) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149477111759274837658807850674 : ((False ∧ (False ∨ (p4 ∧ ((p5 ∨ ((p4 ∨ p3) ∨ ((p3 ∨ False) → ((p1 ∨ True) ∧ (False → p2))))) ∧ p2)))) ∨ (((p4 ∧ p5) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657128006379442383219241550799 : ((((((p3 ∧ p3) → p1) ∨ (((False ∧ ((False ∨ (False → p5)) → (p2 ∧ p1))) ∧ (False → (True ∧ p3))) ∨ (p4 → True))) ∨ (p3 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114065708662029254312142395641 : ((((((((p3 → p2) ∨ True) → p3) ∧ p4) ∨ p2) ∨ ((p4 ∨ (((True → False) ∧ p5) ∨ p2)) ∨ p1)) ∨ ((p2 ∨ True) ∨ False)) ∨ (True ∧ p2)) := by
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
theorem thm_5_vars_688644842661559445052258227808 : ((((p5 ∨ ((p5 ∧ True) → (False ∧ ((False ∨ p1) → ((p5 ∨ p3) → (p4 ∨ p4)))))) ∧ (((False ∨ p5) ∨ ((p1 → p3) ∧ p3)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218047753885991446006298698891 : (((p2 ∨ p5) ∧ (True ∧ p4)) → ((((p2 ∨ (((p1 ∧ p5) → (p4 ∨ p5)) ∧ p4)) ∧ p3) ∧ ((False ∨ p4) → (p5 → p3))) ∨ (False → p5))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319546299010892769996614720747 : (p4 ∨ (((p4 → (((p5 ∨ p5) ∧ p5) ∨ p2)) → (True → p4)) ∨ (True → (((p1 ∧ (((False ∧ True) ∧ p1) ∨ p2)) → (p5 ∨ p2)) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199490650258724436297547415790 : (((p5 ∨ (True ∨ (p1 ∨ (p1 ∧ p5)))) ∨ False) → (False ∨ (((p1 ∨ (p2 ∧ (p5 ∧ (p2 → p3)))) ∨ True) ∨ (((p2 → p5) → p3) ∧ p4)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
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
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h8 =>
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
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225017512647718613146380002814 : (((False ∧ False) ∧ p1) ∨ ((p5 ∨ (((((False ∧ (False → p5)) ∨ p2) ∧ ((p4 ∨ (True ∧ p4)) ∧ p3)) ∨ p1) ∧ (p4 ∧ p5))) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319170229494646762414178663298 : (p4 ∨ ((((((p1 ∨ p3) ∧ p1) → ((True → p4) ∧ p5)) → p1) ∨ (((p3 ∧ p2) ∧ True) ∧ p5)) ∨ ((p5 ∧ p4) ∨ (False → (p2 ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55718160185242156034314537208 : (((((False ∧ p3) ∧ p3) → p3) ∧ (((p3 → False) → (p5 ∧ ((p3 → True) → False))) → (((True ∧ (p3 ∨ True)) ∧ True) → (p4 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41701472067404044542778782273 : ((((((p3 → True) ∧ False) → (p2 ∨ p5)) → (p1 ∨ (((p1 ∧ (((False → (p1 → p5)) → p5) ∧ p4)) ∧ (True ∧ p4)) ∧ p2))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594801180459929613617640823301 : (((((((p5 ∧ p5) ∨ (p2 ∨ (((p5 ∨ p4) ∨ (p1 ∨ p1)) ∨ False))) ∧ p4) ∧ ((p5 ∧ (p3 ∧ (False ∧ (True → p5)))) → p1)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320455035873175986215853447387 : (p4 ∨ ((p5 ∨ p4) → (((((((p2 ∧ p1) → False) ∧ (((p5 ∧ False) ∨ True) ∨ (p3 ∧ p2))) ∧ p5) → (False ∧ (p5 → p2))) ∨ True) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165533553630616052539270084675 : (((p1 → (p3 ∨ (p2 → (p3 → (True → (p4 ∧ p5)))))) → ((True ∨ p5) → (p3 ∨ p2))) ∨ ((True → (p2 ∨ ((p4 ∨ p2) ∨ p2))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69357040844479570781918887533 : ((p5 → (p4 ∨ ((p1 ∧ (False ∨ ((p1 → (True ∧ False)) ∨ ((((p4 ∨ False) → (True → p3)) ∧ ((True ∧ p4) ∨ p4)) ∨ True)))) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257929087075322767549445529155 : ((p4 ∨ False) → (((((p3 → (p1 → p2)) ∧ p5) ∨ (True → (((True ∨ p5) ∧ (True ∧ False)) ∧ (True ∨ p2)))) → p1) ∨ (False → (False → p3)))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158813403578760532887226413385 : ((p5 ∧ (p2 → (((False → False) → (((p2 ∨ p3) → (False ∧ False)) ∨ ((p1 → True) → False))) ∨ p5))) ∨ ((p3 ∧ (True ∨ (p1 ∧ True))) → p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221114888862631784458169437157 : (((True ∨ True) ∨ p1) ∧ (((((p5 → (True ∨ (p5 ∧ True))) ∨ p4) → (((False → ((True ∨ p3) ∨ p2)) → (p5 ∧ p5)) ∨ True)) ∨ True) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117630060547315223461154681381 : ((p3 ∧ (((p5 ∨ (True → (((((False ∧ p1) ∨ (p2 ∨ p5)) ∨ p4) → (p5 ∧ False)) ∨ (p1 ∨ p5)))) ∧ (True ∧ p5)) ∨ p2)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657682460074010628542058164958 : (((((True → p4) → (((p5 ∧ (p1 ∨ ((p1 ∨ True) ∨ (p3 → ((p1 → (True ∧ (p3 ∧ False))) ∨ p4))))) ∨ p3) ∨ p1)) ∨ (p4 ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_147798235658152389669446628762 : (((p1 ∧ ((False ∨ (((p4 ∨ (p4 ∧ (p4 ∨ (((True → p4) ∨ p5) ∧ p5)))) ∨ p1) ∨ p4)) ∨ p4)) → p5) ∨ (p2 ∨ ((p2 ∧ p3) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150316034639565813466042257467 : ((p4 → (p4 ∧ (((False ∨ p4) ∧ (p1 → p2)) ∨ ((((p1 ∧ False) ∨ (p3 ∨ p2)) ∧ (p3 → p3)) ∧ True)))) ∨ (False ∨ ((p5 ∧ p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708432454673168143535560992741 : (((((p1 ∨ (((p5 ∧ p3) → p4) ∨ True)) ∧ p4) → ((((p1 ∨ p4) ∧ ((((p4 → False) → p2) → p3) ∨ False)) ∨ (p3 → p3)) ∨ p5)) ∨ p3) ∧ True) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196130877411690810263281835430 : ((True ∨ (((p1 ∧ (p3 ∧ p4)) ∧ p1) → False)) ∧ ((p4 ∨ (p5 ∨ (((False ∨ (p3 → (True → p5))) → (p3 ∨ (False ∨ p5))) ∨ True))) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_618924252827733847733570879474 : (((((p5 → (False ∨ False)) ∧ (((p4 → (((p5 → p5) ∧ (((p3 → False) ∧ p1) ∨ (p2 ∨ (p5 ∧ p1)))) ∧ p3)) → p4) → p4)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148194720285573491395054173845 : ((((p4 → (p2 ∨ True)) ∨ (False → (((p4 ∧ True) → p2) ∨ (p5 → (p5 → p1))))) ∧ ((p1 ∨ p2) ∧ p1)) ∨ (p3 ∨ ((False ∨ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43828043281943436149699066526 : (((((((p3 ∧ p5) ∨ (True ∧ p3)) ∧ (((p2 → ((p3 ∧ False) ∧ p1)) ∧ (True → True)) ∧ (p5 ∨ p5))) ∧ p3) ∧ (False ∨ True)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



