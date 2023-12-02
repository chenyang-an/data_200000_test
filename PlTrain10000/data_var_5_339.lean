variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149098409106006715517564795484 : (((p3 ∨ (p1 ∧ p5)) → ((False ∧ (p1 ∧ ((False ∧ (((p4 → p5) ∨ (p4 ∨ p3)) ∨ p1)) ∧ True))) ∨ False)) ∨ (p3 → ((p2 → True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166425981404946689068107725084 : ((p1 ∨ ((p2 ∧ False) ∧ (p1 ∨ (p3 → ((p4 ∨ ((p2 → (p3 ∨ p4)) ∧ True)) ∧ p2))))) ∨ (p1 → (p1 → (p1 → (p1 ∨ (p2 ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148988799036656380946930209039 : (((p2 ∨ (True ∧ p4)) ∧ (False ∧ ((True ∧ p1) ∨ ((((p4 ∧ p3) ∨ (p3 → (p2 ∧ p5))) ∨ True) → p2)))) ∨ (((p3 ∧ p1) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611979391828540074262467531862 : (((((((p2 ∧ (p1 → (p3 → (True → p4)))) ∨ (((p1 ∨ True) ∨ p3) ∧ (p1 ∧ ((p3 ∧ False) ∧ p4)))) ∨ p2) ∧ (p3 ∨ p2)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_191384792248938604689651591910 : (((p4 → p1) ∨ (p2 ∨ (((False ∧ False) ∧ p1) ∧ False))) ∨ ((p3 → (False → p2)) ∧ ((p4 ∨ (p1 → p1)) ∨ (p4 ∨ (p4 → (p4 → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154185672780829791153310534275 : ((((((False ∧ p1) ∨ (p1 ∧ True)) → ((p4 ∨ ((True → p1) ∧ p4)) ∨ True)) ∧ (p3 ∨ p1)) ∨ True) ∧ (p1 ∨ ((False → p4) ∨ (True → p5)))) := by
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
theorem thm_5_vars_50011030509297887285843328784 : (((((((False ∧ p5) ∨ False) → p2) → False) ∧ ((p2 ∧ (p2 → (p1 → (p3 ∨ p3)))) → (p3 ∨ p5))) ∧ (p2 ∧ ((True ∧ p1) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219241401284322241191119640495 : ((p1 ∨ ((p2 ∧ p2) → p1)) → ((p4 ∨ p2) ∨ (p5 → (((p4 ∨ ((p3 ∧ p4) → (True → ((False ∧ p4) ∨ p2)))) ∨ p2) → (p3 ∨ p5))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
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
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175382050421628003613694242341 : ((True → (((p3 ∨ False) ∨ (p5 → p4)) ∧ ((((p3 ∨ False) ∨ p5) ∨ p1) → p5))) → ((False ∨ (p2 ∧ ((True ∧ (p3 ∨ p2)) ∧ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342018928904702503485007319435 : (p2 → ((p5 ∨ (p3 ∨ (p5 → ((p1 ∨ ((p3 ∧ p3) → False)) ∧ ((p5 ∧ p3) → ((p1 ∧ (p1 ∧ True)) ∧ True)))))) ∨ ((p1 ∨ p2) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204656173869633044703339628550 : (((p4 ∧ ((p2 ∧ p5) ∧ p2)) ∨ False) ∨ ((((p5 ∨ (((p1 ∧ True) ∨ (p4 ∨ (p2 → p1))) → False)) ∧ p1) → (p5 ∧ (False → p4))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : ((p1 ∧ True) ∨ (p4 ∨ (p2 → p1))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- False on the left can always be used.
    apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624828946777518535899504057253 : ((((p5 ∨ (((p3 → (p3 ∨ ((((False ∨ p1) → p5) ∧ (False ∨ p4)) ∧ True))) → ((True ∨ (p3 → p1)) ∧ p5)) ∨ (p3 ∨ p3))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652185877802230220240014614482 : ((((p2 ∧ ((False ∧ (((p2 ∧ (((p4 ∨ False) ∧ ((p3 ∨ False) → False)) → False)) → (p3 → p5)) → (p3 ∨ p5))) ∨ p1)) ∧ (p5 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261447865893664887115158938491 : ((p5 → p2) → (((False ∨ (((p5 → (False ∨ ((True ∧ False) ∨ p1))) ∧ p1) ∧ p4)) ∧ ((True → (p1 ∧ (p5 ∨ p5))) ∧ True)) ∨ (True ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731442322826943060373516449631 : ((((True → (p3 ∧ p4)) → (((True → (p2 ∨ (False ∧ p3))) ∨ ((((False → False) ∧ (True ∨ False)) ∧ p1) ∨ p4)) → ((p3 → p4) ∨ True))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115464687700013672932292167381 : (((p3 ∧ ((True → False) ∧ (p2 ∧ (p1 → p4)))) ∨ ((p5 → False) ∨ (((p4 ∨ p4) → (False ∨ False)) ∧ (True ∨ (False ∨ p2))))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749765968196263981898681958583 : (((True ∧ (((False ∨ (False ∨ p4)) ∧ (True ∧ ((p4 ∨ (((p1 ∧ False) ∨ (p3 ∧ (p3 ∨ p5))) ∨ (p3 ∨ p1))) ∧ (p3 ∨ False)))) ∨ True)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119358267507940950452619344409 : ((p3 → (p1 ∧ (p4 ∧ ((True ∨ (p3 ∧ ((p1 ∨ p1) ∧ ((p1 ∧ (True ∨ (p3 → (p4 → p3)))) → p5)))) → (False ∧ p5))))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160506129857282660560624993247 : ((((True → p2) ∨ ((p3 ∧ p4) ∨ (((p5 → p5) ∧ False) ∨ p2))) ∧ ((p3 ∨ (True → p3)) ∨ p1)) → ((((p1 ∧ True) ∨ p5) ∧ p4) ∨ True)) := by
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
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h23 =>
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
theorem thm_5_vars_148092637739629935174642720128 : (((((p4 ∨ p1) ∧ ((p3 ∧ p1) → (True → (((p2 ∨ (p3 → False)) ∨ p2) ∧ p1)))) → p5) → (p2 ∧ p5)) ∨ (True ∨ (True → (p3 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180873711654165632665310947892 : (((p2 → (p4 → False)) ∨ ((((p2 ∨ False) ∨ True) ∨ (True ∨ False)) → p4)) → (((True → (True → False)) ∧ True) → ((p1 ∨ (p5 → p4)) ∧ True))) := by
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
  cases h1
  case inl h5 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- False on the left can always be used.
    apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310974551127029364816456206134 : (p2 ∨ ((True → True) ∧ (((False ∧ (p1 → p5)) ∨ ((False ∧ (p1 ∨ p2)) ∨ (((p2 → p1) → (True → (p4 ∨ p5))) ∧ p1))) ∨ (False → p2)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138830273465225193907166612717 : (((p3 ∧ ((p2 → (p1 ∧ False)) ∧ ((p5 ∨ True) ∧ ((((p3 → (False ∧ (False → False))) ∨ True) ∨ p2) → p2)))) ∧ p3) → ((False ∧ p2) ∨ p5)) := by
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
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h12 : (((p3 → (False ∧ (False → False))) ∨ True) ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h13 := h9 h12
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h14 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h15 := h6 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327101858893457422392204637477 : (True → (((p1 → False) ∧ ((True ∨ (p3 ∧ ((p4 ∨ p5) → ((p4 ∨ p5) → (((False → True) ∧ p5) ∨ p2))))) → (p3 ∧ (p5 ∧ p5)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338252178790767058377878279299 : (p1 → ((p3 ∨ (p3 → (p1 ∧ (False ∨ p2)))) ∨ (((False ∨ (p1 → False)) → ((p3 ∨ p2) ∧ (p2 ∨ p3))) ∨ (p1 ∧ ((p5 ∨ p5) → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149650526074267556371666903044 : ((p4 ∧ ((False → ((p2 ∧ True) → (True → p5))) → (p5 ∨ ((p3 → ((True ∨ (p3 → p1)) ∨ p4)) ∧ False)))) ∨ (True ∨ (p4 ∨ (False → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336158420616118541858498635990 : (p1 → ((((((((((p5 ∧ ((True ∧ p5) ∨ p2)) → (p5 → True)) → p1) → p3) ∧ p4) → p1) ∨ True) ∧ ((p1 → False) → p4)) → p5) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117552590322420572570201322064 : ((p2 ∧ ((((False ∨ (p4 ∨ ((p4 ∨ (p3 ∧ True)) ∧ p2))) → p4) → True) ∧ (False ∨ (p1 ∧ (p4 ∧ (False ∨ (False ∨ p1))))))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697266068693933114007850938888 : (((((p5 ∧ p2) ∧ (p2 ∨ (((p5 ∨ (p2 → p5)) ∧ True) ∨ p1))) ∧ (((False → p3) ∨ (p5 → True)) ∧ (((False ∨ True) ∧ p4) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50389646583790468738824177330 : ((((p4 ∨ p2) ∨ (((True ∧ False) ∨ (p1 ∨ (p1 → (False ∧ p3)))) ∧ ((p5 ∨ (p4 ∧ p3)) → p2))) ∨ ((True ∧ (p4 ∨ p4)) → p4)) ∨ p3) := by
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
    exact h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52992760421984302570994962514 : (((((p3 → (False ∨ p5)) → (p4 ∧ (p1 ∨ p1))) ∨ (False ∧ p3)) ∧ (False ∧ ((p3 ∧ (True ∨ (p2 ∨ (p2 → p5)))) ∨ (True ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328896048520883738838056157643 : (True → ((p3 ∧ (((False ∧ p2) ∧ p4) ∧ (p3 ∧ p1))) ∨ ((p5 ∨ (p4 ∨ ((p5 ∨ p3) ∧ (p4 ∨ (True ∧ p2))))) ∨ ((False → p4) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118689593808374748035063964553 : ((p5 ∨ ((((((p3 → (False ∨ ((p5 ∧ p4) ∧ p3))) ∧ p5) ∨ ((p1 ∨ (True → p5)) ∨ (False → True))) ∨ p4) ∧ p3) ∨ p4)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225206714952890361204852929906 : (((p4 ∧ p5) ∧ p5) ∨ (p2 ∨ (((p3 ∧ (p1 ∧ (p1 ∧ p5))) ∨ p4) ∨ (p2 ∨ ((p1 ∧ (p5 ∧ p4)) ∨ ((p3 → (False ∨ p1)) → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_637403056271167884662735741390 : ((((((p2 ∧ (((p4 ∧ p3) → True) ∧ (p2 ∧ p4))) → False) ∧ ((p2 → p1) ∧ ((((p1 ∨ True) ∧ True) ∨ (p2 ∨ p3)) ∨ p1))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304710704265194306894024077493 : (p1 ∨ ((((p1 ∧ p1) ∨ (p5 ∧ ((p4 → (True → p3)) ∧ (((p3 → p5) → (p3 → (p3 ∧ True))) ∨ p5)))) ∨ (p2 ∨ p2)) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228998506392475979223693540590 : ((p5 ∨ (p1 ∧ p1)) ∨ ((((((p1 ∨ (p4 ∨ p3)) ∨ (True ∨ ((p1 ∨ (p3 ∧ p3)) ∨ ((True → True) ∨ False)))) → p1) → p3) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306652212507064473169830813138 : (p1 ∨ (True ∧ ((p1 ∨ ((p4 ∨ p2) → (p1 ∨ ((p5 → ((p1 ∨ p5) ∨ ((p3 ∧ False) ∧ False))) ∧ True)))) ∨ (((p4 ∨ p2) ∧ p4) ∨ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206526997197784542776748684867 : ((True → ((True → (False → p2)) ∧ p1)) ∨ (p1 ∨ (False ∨ (True → ((((((p4 ∧ False) ∧ True) ∨ (p5 ∧ p4)) ∧ (p3 ∧ False)) ∧ p2) ∨ True))))) := by
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
theorem thm_5_vars_68867474264150664807735002399 : ((p4 → (True ∧ ((p3 ∨ (p3 ∨ p5)) ∧ ((((True ∨ ((((p2 ∧ p1) → True) → (p4 → p4)) ∨ True)) ∨ p3) ∧ True) ∧ (False ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206012100387892754946337506146 : ((p2 ∧ ((False ∨ (p3 ∧ p1)) ∧ p4)) ∨ (p2 ∨ ((False → (((False → p1) → (p2 ∨ (p3 ∧ False))) → (((p2 ∨ p4) ∨ p4) ∧ p3))) ∨ False))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694264780712673007817737522625 : (((((p3 → ((p3 ∧ p4) ∧ p3)) → ((p2 ∨ (False → (p1 ∧ p3))) → False)) ∨ (True → (((p4 ∨ True) ∧ ((p2 → False) ∧ p5)) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759944316525589692289499240492 : (((p2 ∧ ((((p5 ∧ True) ∧ p1) ∧ p3) ∧ (p3 ∧ (p1 ∨ ((((True ∨ p2) ∧ ((p5 ∨ (False ∨ (p1 ∧ p3))) ∨ True)) ∧ p3) → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319377310296899372834977708973 : (p4 ∨ ((False ∧ (((p4 ∨ (((True → (False ∧ p3)) ∧ p5) ∧ p5)) ∧ p3) ∨ p1)) ∨ (((p1 → p4) → p5) → ((p2 → (p5 → True)) ∨ p1)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255495902272440496644400033359 : ((p5 ∧ p2) → (((False ∧ ((p1 ∧ p1) ∧ (p4 → (((((p4 → p1) ∧ p5) ∨ p2) ∨ (p2 → p4)) ∧ (p2 → p3))))) ∨ p1) ∨ (p3 ∨ True))) := by
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
theorem thm_5_vars_218528370685595751262012164293 : (((p4 ∨ p2) → (p5 ∧ True)) → (p5 ∨ ((p1 → (False ∨ (p2 → (((p5 ∧ ((((p2 → p1) ∨ p2) → p4) ∧ False)) ∨ p3) ∨ p5)))) ∨ p1))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (p4 ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111555322452494990093265537387 : ((((((((True → False) → (p4 ∨ False)) → (True ∨ p1)) ∧ ((p5 ∧ True) ∨ p1)) ∨ ((False ∧ (p3 ∨ p1)) → p4)) ∧ p5) ∨ p2) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_470489536303303330775841285980 : ((((((p4 ∨ (p1 ∧ (p1 ∧ p4))) ∨ p2) ∨ ((False ∧ p5) ∨ True)) ∧ ((((p1 → p2) → (p4 ∧ p4)) ∨ p4) → ((p4 ∨ p3) ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183878011735455571115152154654 : ((((p4 → (p5 ∨ p4)) ∧ (((p5 ∧ p3) ∧ p4) ∧ True)) ∧ p1) ∨ ((True ∨ (p1 ∧ (((p4 ∧ (p4 ∧ p1)) → True) ∨ (p2 ∨ p2)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306029817197174044624467118217 : (p1 ∨ ((((p5 ∧ p2) → p5) ∧ True) → ((p2 → (((((True → ((True ∧ p4) → False)) ∧ (False → False)) ∧ (p1 ∧ p4)) ∨ True) ∨ True)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69319859436868664042767573729 : ((p5 → (p4 ∧ (((p3 → ((True ∨ (p2 ∧ False)) ∧ (p2 → (p3 ∧ p3)))) ∨ (p4 ∧ p5)) → ((p2 ∨ p2) ∨ (p4 ∨ (p1 → p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37177107955004528225551369708 : ((((((((p2 ∨ p1) → p4) → p3) ∨ ((True → (p1 ∨ p1)) ∧ p3)) ∨ (((p5 ∧ p3) ∧ (p3 ∨ (p1 ∧ p4))) ∧ p1)) ∧ True) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192278872888507664452569949132 : ((((False → False) ∧ ((False ∨ (False ∧ p3)) → p2)) ∧ p5) → (((True → (((False → ((p2 → p3) ∧ p5)) → p2) → p3)) ∧ False) ∨ (False → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668800094704615071912309913072 : ((((((((p4 → p2) ∧ p5) ∨ (p3 → (p1 ∧ ((p5 ∨ p1) → (p5 → False))))) ∨ (p5 → (True → p3))) ∨ p5) ∨ (False ∧ (p3 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234151680459499266125310682271 : ((True → (False → p4)) → ((((((p1 ∨ (p2 ∧ (p3 ∧ (False → p1)))) ∨ (False → (p1 → True))) ∨ p3) → (False ∨ (p5 → p4))) ∧ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39338167023425544398315918727 : (((p2 ∧ ((p4 ∧ (p4 ∧ p4)) → (p5 ∨ (((((p3 → (p2 ∧ p5)) ∨ p3) → (True ∧ ((p1 → p3) ∨ p1))) ∨ p4) → False)))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781919521806600496050727543422 : (((p2 ∨ (p2 → ((((p5 → (False ∧ p2)) ∨ p3) ∨ (False ∨ p2)) ∧ (p1 → ((p5 ∨ (p3 → (p5 ∧ (p2 ∨ (p4 → p1))))) ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40537088442648462966073412004 : ((((p3 ∨ (((p5 → ((True ∧ (p5 ∧ (p1 → p3))) ∧ (p1 ∨ p3))) → ((False ∨ p2) ∧ (p5 ∨ p1))) ∧ (p5 → p3))) ∨ p3) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199615439242887717131281043714 : ((((p4 → ((p5 ∨ p2) → True)) → p2) → p5) → (p4 ∨ ((p4 ∧ (p3 ∧ (p5 ∨ p1))) ∨ ((p3 ∧ (p4 → p4)) → ((p3 ∨ p5) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157570117528160513589772921485 : ((((False ∧ (True ∨ (p3 ∨ p5))) → (p1 → (p3 ∧ (((False ∨ p1) ∧ p3) → p1)))) → (False ∨ False)) ∨ (True ∧ (True → (False ∨ (True → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306567005384614506346601969779 : (p1 ∨ ((p2 ∨ p1) → ((p1 ∧ ((True → p4) ∨ True)) → (((False → ((False ∧ p4) → ((p1 ∨ (True ∧ p1)) ∧ p2))) ∧ (p2 ∧ False)) ∨ p1)))) := by
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
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65758009548979778722981952357 : ((p4 ∨ (((((p2 → False) ∧ p1) ∧ p1) ∨ ((((p4 ∧ True) ∨ (True ∧ p3)) ∧ (p4 ∧ True)) ∨ True)) ∨ (False → (p5 → (False → p1))))) ∨ p1) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69207070623900731602941723310 : ((p5 → ((((True → p5) ∧ ((False ∨ p5) → True)) ∧ p3) ∨ (True ∧ ((p4 ∨ p1) ∨ (p4 ∧ (False ∧ ((p1 ∧ (p2 → p5)) → False))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739271616065735297020985871649 : ((((p4 ∧ p2) ∨ (((p1 ∧ False) → p1) → (((True ∨ (p4 → (p3 → ((p1 → p5) ∨ p3)))) → (p1 ∧ p2)) ∨ (False ∨ (p2 ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_461229866757098520468328940005 : (((((((p1 ∧ p4) → p4) → (((p5 → (p3 ∧ p1)) ∨ p2) ∨ True)) ∨ (False ∧ p5)) ∧ ((((p1 ∧ p2) ∨ (p1 ∧ p2)) → False) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110925498984019385118476327949 : ((((p4 → ((p1 ∨ ((p5 ∧ False) ∨ (((p1 ∨ p5) ∧ (p4 ∧ (p4 ∨ ((p1 ∨ p5) ∧ p5)))) → False))) → p1)) → p5) ∧ p4) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51916383011310318362593029863 : (((((p3 ∨ ((((p2 ∧ p5) ∨ p1) ∨ (p3 → p5)) ∨ p2)) ∨ False) → (p1 ∨ p5)) ∨ ((((True ∧ (p3 ∨ p2)) → True) ∨ p3) ∨ p1)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78708315926990086635676322587 : (((((p3 ∨ p1) → (((p2 → p3) → (p1 ∧ (p4 ∧ False))) ∨ (True → False))) ∨ ((p5 ∧ (p1 → (p1 ∨ False))) ∧ p1)) ∧ (p3 ∨ False)) → p5) := by
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
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h6 : (p3 ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h7 := h4 h6
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h9 : (p2 → p3) := by
          -- Implications on the right can always be decomposed.
          intro h10
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h11 := h8 h9
        -- We need to get the right conjuct of h11 based on <expert-advice>.
        let h12 := h11.right
        -- We need to get the right conjuct of h12 based on <expert-advice>.
        let h13 := h12.right
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h15 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h16 := h14 h15
        -- False on the left can always be used.
        apply False.elim h16
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h19.left
    let h22 := h19.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h23 =>
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h24 =>
      -- False on the left can always be used.
      apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133681141892493049809550026115 : (((((p1 ∧ (((p1 ∧ (p4 ∧ True)) ∧ p2) ∨ (p2 ∨ True))) ∨ ((p3 → p2) → p4)) ∧ ((p2 ∨ p1) ∧ p5)) ∧ p4) ∨ ((False → p2) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766838320130660067881009735680 : (((p4 ∧ (p4 ∨ ((p2 ∨ ((p1 ∨ p1) ∨ ((((p5 → p1) → (p3 → p1)) → (p2 ∧ p3)) ∨ (True ∧ p2)))) ∧ ((p1 ∨ p1) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753159176229086278103331496750 : (((False ∧ ((((((p3 ∧ (False → (((False → False) ∧ p4) ∧ p1))) → False) ∨ False) ∧ p4) → ((p2 ∨ (False ∧ False)) ∧ p3)) ∧ (True → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734239819578542628403683110921 : ((((False ∨ False) ∧ (p4 ∧ (p1 ∧ ((p2 ∨ (((True ∨ False) ∨ True) ∨ ((p3 ∨ p5) ∧ p5))) → ((p5 ∨ p5) → ((p4 ∨ p5) → p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670733052312795463003163474057 : ((((True ∧ (p3 ∧ ((p1 ∨ True) ∧ ((((p5 → p3) → p1) → ((p4 ∧ (p2 → p3)) ∧ False)) ∧ (p1 ∧ True))))) ∨ ((p4 ∨ True) ∨ False)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_767515483406459065722873172184 : (((p5 ∧ (((((((p3 ∨ (True ∨ ((True ∨ p1) → p1))) ∧ p2) ∨ (p4 ∨ p1)) ∨ False) ∧ ((p1 ∧ (p4 → p2)) ∨ p3)) → False) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214458376207606683552543064031 : (((True ∧ False) ∧ (p5 ∧ p1)) ∨ ((p3 ∧ p5) ∨ ((False ∧ ((p2 ∨ (False ∨ p5)) ∨ (p5 ∧ False))) → (p2 ∨ ((True → (p3 → p1)) ∨ p4))))) := by
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57087976532183693665968894663 : ((((p2 ∧ p3) ∧ p5) ∨ ((((False ∧ (((p5 ∧ p1) ∧ p1) ∨ ((True ∧ p3) ∧ p3))) ∨ p2) ∨ ((False ∧ p5) ∧ (p4 ∧ True))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601813098206881977346835888200 : ((((p4 ∧ ((p5 ∧ (((((p1 → p2) ∨ (p4 ∧ ((p5 ∧ p1) → (False ∨ p2)))) ∨ p4) → p1) ∨ p3)) ∨ (p4 ∧ (True ∨ p4)))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630288429971745947067663402986 : (((((True ∧ (p5 → (((((p5 ∨ p5) → (p1 → p3)) → (p1 → (p2 ∨ p3))) → False) ∧ (p5 ∨ (p3 ∧ (p5 → p2)))))) ∨ p2) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330375432898745544117777859478 : (True → (p2 ∨ ((False → ((False ∨ (p3 → p5)) ∨ (p5 → ((p5 ∨ (p3 ∧ p5)) ∧ ((p2 → p4) ∨ p2))))) → (p5 ∨ ((p1 → p1) ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717888952929498607897875228070 : (((((p1 ∨ (False → p5)) ∧ p3) ∨ (True ∧ (((True ∨ ((((True → (False ∧ False)) ∧ False) → True) ∨ True)) ∨ (p2 → p1)) → (p5 → p5)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h7 =>
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249023287332597339650269862618 : ((p4 ∨ False) ∨ (True ∧ (((((((True ∨ p4) ∨ p1) → p3) ∨ False) → ((p5 → p2) ∨ (False ∧ (p2 → p4)))) ∨ p5) ∨ (True → (p4 → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213795407105275256814575151433 : (((p2 ∧ (True ∧ p3)) ∨ p4) ∨ (p2 ∨ ((p4 ∨ (p4 → (True ∧ (((p5 ∨ p4) ∨ (p5 ∨ (p1 → (False → (p2 → p1))))) ∧ p4)))) ∨ p2))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190824861365336639341620640617 : (((p2 ∨ ((p2 ∧ (p4 ∧ True)) ∨ p3)) ∨ (p5 ∧ p2)) ∨ ((((((False ∨ ((True ∧ (p4 → True)) ∧ False)) ∨ True) ∨ p3) ∨ False) → True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179598805440948702564796074468 : ((p3 → ((p1 ∨ (p4 ∧ (p2 ∧ p2))) ∧ (p3 ∧ (p2 ∧ (p4 ∧ False))))) ∨ (p5 ∨ (p4 → ((p4 → p3) ∨ (((p1 ∧ p5) ∨ True) ∧ True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150319834048721937154303067329 : ((p4 → (p3 ∨ ((True ∧ (((True ∨ p1) → p3) ∧ True)) → ((((p5 → p4) ∨ True) ∧ p4) ∧ (p1 ∧ p5))))) ∨ ((True ∧ True) → (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754296302780841227332907107329 : (((False ∧ ((True ∧ p3) ∨ ((True ∧ (((True ∨ (((p5 ∧ p1) → p2) → p1)) ∧ (((False ∨ p4) → False) ∧ p3)) → p5)) → (False ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59963222419898740870383266531 : (((True ∨ p5) → (((True ∧ ((p2 ∧ p1) ∨ ((((p4 ∧ p2) ∧ False) → p3) ∨ (p2 ∧ (((p4 ∨ True) ∨ p5) → p3))))) ∧ p5) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307204066112877603975885963740 : (p1 ∨ (p1 ∨ ((p1 ∨ (p5 ∨ ((p2 → (p2 ∨ (p5 → p2))) ∨ p3))) ∧ (((p5 ∨ ((p2 ∨ p3) → (p1 ∨ (p5 → p5)))) ∨ p4) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62254881684888511937304919317 : ((p3 ∧ ((p4 ∨ (p4 ∨ (((p2 → ((((True ∧ ((p2 ∧ p2) → p4)) → p5) → p4) ∧ (p3 ∧ p4))) ∨ (p1 ∨ True)) ∧ p3))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66588202685931978523499395536 : ((True → ((p5 ∨ (((((p2 ∨ p1) → p3) → (p3 → p2)) ∧ (p4 ∨ (True ∨ (p1 ∧ (p1 ∨ False))))) ∧ True)) ∧ (p3 ∧ (p4 ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180732025593766203165416424540 : ((((False ∧ (p2 ∨ p1)) ∧ p1) ∨ ((True → p5) ∨ (p4 ∧ (p2 → p3)))) → ((((p2 → p3) ∨ (p5 ∨ (p4 ∧ p5))) ∧ (p3 ∧ False)) ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340704263264583073373572140149 : (p2 → (((((p1 → p2) ∨ ((p4 ∨ False) → ((True → (p3 → (False ∧ (p1 ∨ (p4 ∧ False))))) → p2))) → ((p2 ∨ p4) ∧ p3)) ∧ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64440490213371378688283760715 : ((p1 ∨ (((((((p3 ∧ p4) → (p3 ∧ p4)) ∨ p4) ∨ p5) ∨ p2) → (p2 ∧ (((False → (True ∧ p5)) → p5) ∧ p3))) ∨ (p3 → True))) ∨ p5) := by
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
theorem thm_5_vars_179211891875454550196848716565 : ((p4 ∧ ((((p2 ∧ p2) → p4) ∨ (p5 ∧ (p3 ∨ (p4 ∨ False)))) → p3)) ∨ ((p1 → (True → ((((p2 ∨ p3) ∧ p2) ∨ False) → p1))) ∨ p3)) := by
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
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64156576382230605023678079243 : ((False ∨ ((p2 ∧ p1) ∧ ((p4 → (p4 ∧ (p4 → p3))) ∧ ((p5 → (((p1 ∨ (p3 → True)) ∧ (True ∨ p2)) ∧ False)) ∨ (p3 ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745488177134942807326812687713 : ((((True ∨ True) → ((((p1 → p1) ∨ False) ∨ p3) ∧ (((((((p5 → p3) → p4) ∧ (False → p5)) → p1) ∨ p2) ∨ (p3 ∨ p5)) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232191644511145310827375874835 : (((False → p2) → False) → ((((((True ∨ (((p5 → p2) ∧ True) ∨ p1)) ∧ (p4 ∨ p5)) → (p3 ∨ (p2 → p2))) ∨ True) → (False ∨ p1)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308427938091427844056170125875 : (p2 ∨ (((((p1 ∨ p2) ∨ ((p2 ∨ p4) ∧ p2)) → (p3 ∧ (p1 → (((((p5 ∨ p1) → (p4 → p3)) → p4) ∧ False) → p5)))) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53124033368418429517414522866 : (((p5 → (p2 → (((True → False) ∨ (p3 ∧ p3)) ∧ (p1 ∧ p1)))) ∧ ((p5 ∧ ((p3 ∨ (p2 ∨ (p2 ∨ (True ∨ p2)))) ∧ True)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647696570573851674765841981148 : ((((p5 → ((False → True) → ((p3 → (True → (p3 ∨ (True ∧ (((p3 ∨ (p5 → p1)) ∧ p4) → (p4 → p3)))))) ∧ (p2 ∧ True)))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



