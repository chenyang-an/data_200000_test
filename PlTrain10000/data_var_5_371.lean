variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46356092452563984507263940037 : ((((True → (p3 ∨ (p3 ∨ (False → ((p2 → False) ∨ (True ∧ (True ∧ False))))))) → (((True ∧ (p4 → False)) → p1) ∨ p5)) ∧ (p1 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141737736125994330773683679302 : (((True → p1) ∧ (False ∨ ((((p4 → p5) ∨ ((False ∧ ((True ∧ p2) → p2)) ∧ False)) ∨ False) → ((p1 ∧ p1) ∨ p4)))) → (p3 → (p4 → p1))) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h8
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159998622218805560762732595186 : ((((p1 → (False ∧ (p4 ∧ (p5 → p1)))) ∨ (((((p4 ∧ p2) ∨ p2) ∧ p3) → p5) ∧ p2)) → True) → (p2 ∨ ((p4 ∨ (p3 ∨ True)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_615193440662598259562187368106 : ((((((p4 ∨ (p3 ∧ False)) ∧ (((((p3 ∧ (p4 ∧ p3)) ∨ True) ∨ p4) → False) ∧ False)) ∧ (p2 ∨ (((p2 → True) → p4) → p3))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_265753943082208437426306500022 : (True ∧ (p4 ∨ (((((p4 ∧ (((p2 → p4) → False) ∧ False)) ∨ ((p4 → p3) ∨ (p1 → (p1 ∧ True)))) → ((p2 → False) ∧ False)) ∧ p3) ∨ True))) := by
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
theorem thm_5_vars_714604461721477164370662896228 : (((((p5 ∨ p3) ∨ (p1 → (True → p1))) → (p1 → (((False ∨ (p1 → (p2 ∧ False))) ∨ p1) ∨ ((p5 ∨ (False → (p4 ∧ True))) ∧ True)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659319927207252031867400752848 : ((((p5 → ((True → (True ∧ p1)) → ((((p2 ∨ p1) ∨ p2) → (((True → True) → True) ∨ (p4 ∧ True))) → (p2 ∨ p2)))) ∨ (p3 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63068808521950930718585977740 : ((p5 ∧ ((p3 → (False ∧ ((((p1 ∨ (p5 → ((p5 → (p5 ∨ (p3 → False))) ∨ False))) ∧ (p3 → p3)) → False) ∧ (p4 ∨ p3)))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158098000297022484665576229576 : (((((p3 ∧ p3) ∨ p2) ∨ True) ∧ ((((p2 ∧ (p4 ∨ p4)) ∨ True) ∨ ((p5 → p1) ∨ True)) ∨ p2)) ∨ (p3 → (False ∨ ((p1 ∨ p5) → p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50432383519591988267883156532 : (((p5 ∧ (p2 ∧ (((p2 → ((p1 → (False ∨ (p1 → p5))) → p1)) ∧ p4) ∨ ((p4 ∨ p4) ∧ p1)))) ∨ ((p4 ∨ (p4 → p4)) ∨ p5)) ∨ p2) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117623846472845834856699004523 : ((p3 ∧ ((False ∧ (True → (((p2 ∧ ((p2 ∧ p4) ∨ (False ∨ p2))) ∧ ((((p5 ∧ p5) ∨ p4) ∧ p2) ∧ True)) → False))) ∧ p1)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307211880053733038537103878329 : (p1 ∨ (p1 ∨ (((p4 → p4) ∨ p3) → (((((((p3 ∨ True) → False) → p5) ∧ p3) ∧ (p1 ∨ (p5 → False))) ∨ (p3 → p2)) ∨ (False → p2))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305531870353745065120815450079 : (p1 ∨ ((((True ∨ (p1 → p5)) → False) ∧ ((p1 ∧ p3) ∨ ((p4 → False) → True))) → (((p4 → ((True ∨ p4) ∨ p2)) ∨ (p4 ∨ p1)) → p3))) := by
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
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h10 : (True ∨ (p1 → p5)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h11 := h4 h10
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h1.left
      let h15 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h19 =>
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h20 : (True ∨ (p1 → p5)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h21 := h14 h20
        -- False on the left can always be used.
        apply False.elim h21
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h1.left
      let h24 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- One of the premise coincides with the conclusion.
        exact h27
      case inr h28 =>
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h29 : (True ∨ (p1 → p5)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h30 := h23 h29
        -- False on the left can always be used.
        apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618924550430652309947885174008 : (((((p5 → (p1 ∨ True)) ∧ (((((p3 → (p1 → (p1 → p4))) → False) → p3) → ((p5 ∧ (p3 → (p3 ∧ True))) ∧ p4)) → p4)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44120130386728209867806789883 : (((((p5 ∧ ((p2 ∧ ((p2 ∧ p2) ∨ True)) ∧ (p3 → True))) → ((p5 ∨ (False ∧ True)) ∧ (p5 → True))) ∨ (p1 ∧ (True ∨ True))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754066997208440753090516519676 : (((False ∧ (((p2 → (p5 ∧ p3)) → p5) → (p2 ∨ ((((p2 ∨ True) ∨ (False → p5)) → ((p3 → p1) → p4)) ∨ ((True ∧ p5) ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341759434200036727446190104458 : (p2 → ((p3 ∨ (((p5 ∨ p2) → ((((((True ∧ False) → p2) → p5) ∧ True) ∧ ((p4 ∨ p5) ∧ p3)) ∨ (True ∨ p5))) ∨ False)) ∨ (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186316108517936606668955108382 : ((((p3 ∨ (((p3 ∧ p1) ∧ False) ∨ p2)) ∨ (p1 ∨ p1)) → p3) → (p4 ∨ ((p2 ∧ ((((p1 ∧ (True → p2)) → p5) → p4) ∨ p3)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609353170732326471302057054443 : ((((((p1 ∨ False) ∨ (((p2 → p5) ∧ ((True ∧ (p2 → ((p4 → p1) ∨ (True ∧ False)))) ∨ True)) ∨ ((p3 ∧ True) ∧ p2))) ∨ False) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_121691982109683631923315301541 : ((((p4 ∨ (((p4 → (p2 ∧ (p3 ∧ p5))) → p2) → p5)) ∨ (False → ((p4 ∨ p2) ∨ ((p1 ∨ True) ∧ (p4 → p1))))) → False) → (p5 → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p4 ∨ (((p4 → (p2 ∧ (p3 ∧ p5))) → p2) → p5)) ∨ (False → ((p4 ∨ p2) ∨ ((p1 ∨ True) ∧ (p4 → p1))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53990409981097084378173065471 : (((((False ∨ p3) → ((p5 → False) ∨ (p4 ∧ p2))) ∨ True) → (p4 → ((p4 → False) → (((p4 ∧ p2) → False) ∨ (p2 ∧ (p2 ∨ p2)))))) ∨ p2) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52554896388179053381906479010 : (((((p2 ∨ p4) ∨ (((p1 → (p1 → True)) ∧ p5) ∨ (p4 ∧ p2))) → False) ∨ ((p1 ∨ True) → ((((p5 ∨ p3) ∨ p2) → p2) ∨ True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217077092308984352953568700067 : ((((p5 → p1) ∧ p3) ∨ False) → (p1 → ((((p4 ∧ (p2 → p4)) → (((p5 → p2) ∨ ((False ∨ p2) ∨ p4)) ∧ p4)) ∨ (True ∧ p1)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
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
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135904389699932252252558166449 : (((((((False ∧ p1) → p5) ∨ False) → (p5 ∨ p2)) ∧ (False → p2)) → (((p4 ∧ p4) ∧ ((False ∧ p2) ∨ p2)) ∨ p4)) ∨ (True ∨ (p5 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47352348183584183731396135710 : ((((True ∧ p5) ∨ (p3 ∨ ((True → p2) → ((p3 → ((True → (False ∨ (p4 → (False ∨ p4)))) → (p3 ∧ p3))) → p4)))) ∨ (False → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246739237996451838160837675340 : ((p5 ∧ p5) ∨ (((False ∨ (False ∨ (p3 → (((True ∧ p5) → (p2 → p5)) ∨ ((p2 ∧ (p1 ∨ (p3 → p5))) ∧ (True ∧ p4)))))) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184420744278222806146318023711 : ((((((p3 → p4) → p3) ∨ p3) ∧ (p1 ∨ True)) ∧ (p5 ∨ p1)) ∨ (((True → False) ∨ ((False → (p1 ∨ p5)) ∧ (p5 ∧ (True → p2)))) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608969705539843815716636713038 : ((((((p4 → (((p5 → (p2 ∨ p3)) → ((p5 ∨ p5) ∧ True)) → p2)) ∨ ((p4 → True) ∧ (((p2 ∨ p2) ∨ p5) → p1))) ∨ p5) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40901168551493487920744767120 : (((((p2 → False) ∨ ((False ∨ (p2 → ((p5 → (False ∨ p2)) ∧ (p1 → (p4 ∧ p2))))) ∧ ((p3 → p3) ∧ True))) ∧ (p1 ∧ p1)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64965837148026292249438289980 : ((p2 ∨ (((((p2 ∨ p5) ∧ p4) ∨ p5) ∧ p4) ∨ (p1 → (((p2 → p5) ∧ False) ∨ (True → ((((p5 → p4) → False) ∧ p3) ∧ True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648653952279440571753328381790 : (((((((p4 → p4) ∨ p3) → (((p4 ∨ (p4 → p5)) ∧ ((p3 ∨ True) → p1)) → ((p4 → p3) ∨ (False ∨ p4)))) ∨ False) ∧ (p1 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51947434004116944889856528646 : (((((((p4 ∨ p1) → p2) ∨ False) ∨ p4) ∨ (((p3 ∧ p2) ∨ p3) → (p4 → p1))) ∨ ((p1 → (((True ∧ p5) → True) ∧ p1)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305504942249268032131884595719 : (p1 ∨ (((True ∧ p2) ∧ ((((False → p1) ∧ p4) ∨ ((p4 ∧ p1) ∧ False)) ∨ True)) ∨ (p4 ∨ (((p2 ∧ (p5 ∧ (True ∨ p5))) → False) ∨ True)))) := by
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
theorem thm_5_vars_48463945881554374598668966781 : ((((((p3 ∨ True) ∧ ((((p1 → p1) → ((p5 ∨ p2) → (p2 ∨ p2))) ∨ (p4 → p1)) → p1)) → p2) ∧ p2) ∧ (p1 → (p3 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54554563909794775602705565496 : (((p2 ∧ ((p5 ∨ (True → (p1 ∨ True))) → p1)) ∨ (((p4 → ((p5 ∧ (p4 → p5)) ∧ ((False ∨ False) → p1))) ∨ True) ∨ (p5 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56184592720502121899816052482 : (((p3 ∧ (p4 → (p5 ∨ p5))) ∨ ((((((p2 ∨ (p2 → p1)) ∨ p4) → (((p2 ∨ p5) → p1) ∧ p5)) ∨ (p2 ∧ p1)) ∨ p2) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114939298121918657656187576434 : (((((True ∧ (p5 → True)) ∧ True) → ((False → ((p2 ∧ p4) ∧ True)) ∨ p3)) → ((p3 ∧ (((True → True) ∨ p4) ∧ p4)) → False)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42368232513055877118705002404 : (((p4 ∧ ((((False → p5) → (p3 ∨ ((p3 ∨ (((p3 ∨ p4) ∧ (p5 ∨ (False → (True ∨ False)))) ∧ p3)) ∨ False))) ∨ p1) ∧ p5)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178946590059211597285332362802 : (((p3 ∧ p5) ∨ (((False ∧ ((p4 → (False ∧ False)) ∧ p4)) → p1) ∧ False)) ∨ ((((p1 ∧ (p3 ∨ True)) ∨ ((p4 → True) ∨ p1)) → p3) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∧ (p3 ∨ True)) ∨ ((p4 → True) ∨ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118752825968965513853183004937 : ((p5 ∨ (((True → p2) ∨ p4) → ((((p5 ∧ p4) → (False → p5)) → p3) → (p4 ∨ (((False ∧ True) ∨ p2) → (p4 ∧ p5)))))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172682809512733501169565065019 : (((False ∧ p2) ∨ (((p5 ∧ (p1 ∧ (p3 → (p4 ∨ p1)))) ∨ (False ∨ p1)) ∨ p4)) ∨ (False → (((p5 → p3) ∨ p5) ∨ (p4 ∧ (p5 ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206093677265110755576255335339 : ((p3 ∧ (p4 ∨ (False ∧ (p2 ∨ p4)))) ∨ (((p2 ∧ ((((p3 ∧ True) → (p1 ∧ True)) ∨ p3) ∨ (p5 ∧ p2))) ∨ ((False → False) ∨ True)) ∨ p5)) := by
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
theorem thm_5_vars_325891458139288338037072237787 : (p5 ∨ (p4 ∨ ((p4 → p1) → ((((p4 ∧ p1) ∧ ((p1 ∧ (p5 → p2)) → p1)) ∧ ((p5 ∨ ((p2 ∧ p5) ∨ p5)) ∧ p3)) ∨ (p1 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136698397695169190430828870664 : (((False ∧ p3) ∧ (((p2 ∨ ((((p5 ∨ ((p4 ∨ p1) → p3)) → p5) ∨ p5) ∨ ((p5 → p3) → p1))) → p5) → p3)) ∨ (False → (p2 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328331793600493712027793214409 : (True → ((((((((False → p2) ∨ p4) ∨ True) ∧ ((p1 → p4) ∨ True)) → (False ∨ p5)) ∨ False) → (p4 → p2)) → ((p2 ∨ (False ∧ True)) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113957035241710399488749269650 : ((((p3 ∧ p4) ∨ ((((p2 → (p2 ∧ p2)) ∨ p2) → p1) ∨ ((p1 ∧ (p2 → p1)) ∧ (False ∨ p2)))) ∧ (p2 ∨ (True ∨ p2))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158125104037483061145395867544 : (((p4 → (True ∧ (p1 ∨ True))) ∧ (((p3 → ((p4 ∨ p1) → p1)) → (p2 → p5)) → (True → False))) ∨ (((p2 → True) ∨ (p3 → p1)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657403492991361522694313342205 : (((((p3 → p1) ∧ (((p4 ∨ (p2 ∨ (((p5 → p1) ∧ (True ∧ p1)) ∧ False))) ∨ p4) ∧ (p3 ∨ ((p4 → p2) ∨ p1)))) ∨ (p3 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699492462552939844494656570662 : ((((((True ∧ (p5 ∨ p3)) ∨ ((False ∧ p2) → (p5 → False))) ∨ p1) → (((p2 → (False ∧ p4)) ∧ False) ∨ ((p5 → p5) → (p1 → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592521661295706202246475540293 : ((((((p2 → p2) ∨ ((((p2 ∧ (((p5 ∧ True) → (p2 → p5)) ∨ p4)) ∧ (p5 ∨ p2)) → p1) ∨ (p5 ∨ p3))) → (p5 → False)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731331232333542764393647388456 : ((((p4 ∨ (p1 → p2)) → (False ∧ (((p4 ∧ (p2 ∨ (p1 ∧ ((p3 → (p1 ∧ (p4 ∨ p2))) ∨ (p3 ∧ True))))) → (p5 ∧ p1)) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182914684353738920608583221524 : ((((p5 → True) → False) → ((((True ∧ p2) ∨ p2) ∨ False) ∨ p3)) ∧ ((((p4 ∨ p5) ∧ (p5 ∨ False)) ∨ (p5 → (p4 → (p3 ∨ True)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668874344096978498171273624428 : ((((((p3 ∧ False) ∧ (False ∧ ((p5 ∨ p1) → ((((p4 → (p1 ∧ p5)) ∧ (p5 ∨ True)) ∧ p3) ∨ False)))) ∨ True) ∨ (True → (p4 ∧ p4))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_89171326702478582151762346530 : ((((p4 ∨ True) → False) ∧ ((p4 → (((p5 ∨ (True ∧ p2)) → (((p2 ∨ True) ∨ p4) → p2)) ∨ (p2 ∨ p1))) ∨ (p5 ∨ (p5 ∨ False)))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p4 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349963672919462970560862488287 : (p4 → (((False ∧ ((p4 ∧ (((p5 ∨ ((p5 ∧ p1) ∧ (p3 ∨ p3))) ∧ p2) ∨ ((True ∧ (True ∧ p4)) ∨ p1))) ∨ (p2 ∧ p1))) ∧ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347312127322952777803137973212 : (p3 → (((True ∧ ((p5 ∨ p3) ∧ (p1 → p1))) ∧ (False ∨ p5)) → (((True ∨ ((p4 ∨ p4) ∧ (p3 ∧ (p1 ∨ p5)))) → (p2 ∨ False)) ∨ True))) := by
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
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249131105936500272054836001711 : ((p4 ∨ p2) ∨ (((((p1 ∧ p2) ∨ p5) ∧ (False ∧ False)) ∨ (False → p4)) ∧ (True ∨ (((p1 ∧ p1) ∨ (p4 → p3)) ∧ (p5 ∨ (True → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338824716112538457430974494142 : (p1 → ((p4 ∨ p5) ∨ (((p2 ∨ True) ∨ p3) ∧ ((((p5 ∨ p5) ∧ p5) ∧ p3) ∨ (p1 → ((p2 ∨ ((True ∨ p2) ∨ p4)) ∨ (p2 → True))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798027813405429424464033498104 : (((p1 → ((p4 ∧ (((True ∨ (((((p2 ∨ True) ∧ True) → p3) ∨ (p5 ∨ p4)) ∧ p1)) → False) ∧ (p3 ∧ p2))) ∧ ((p4 ∧ p1) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41149527954304092839388159399 : ((((((p5 ∨ True) ∧ False) ∨ (p3 → (((((p4 → p5) → True) ∨ ((True → True) → p5)) → p2) → p4))) ∨ ((p4 → True) ∨ p4)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61228728013136173979552685475 : ((False ∧ (p1 ∧ (p2 → ((((p1 ∨ (p3 ∨ p4)) → p5) → p2) ∧ (((True ∧ p4) → (True ∨ p2)) ∧ ((p4 ∨ p1) ∧ (p5 → p3))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757753381270214723580891634146 : (((p1 ∧ (False ∨ (((p2 ∧ (((p5 ∧ p1) ∨ (p2 ∧ p2)) ∧ False)) ∧ (p1 ∧ (p1 → ((p5 ∨ p4) ∨ p5)))) ∧ (True ∨ (p2 → True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179403874914752609343860250550 : ((p3 ∨ (False ∨ (True → ((((p1 → p4) ∨ (p5 ∨ p4)) → p2) ∧ False)))) ∨ (((((True ∧ p4) ∧ p1) ∨ p2) → p1) ∨ ((False → p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215497532027882552766883057203 : ((p4 ∧ ((p1 ∨ p5) ∨ p1)) ∨ (p5 → ((p2 ∧ (((p5 → p3) ∧ (((p3 → (p1 → p5)) → p5) ∧ (p2 ∧ p4))) → p3)) ∨ (p5 ∨ p3)))) := by
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
theorem thm_5_vars_157506855122664119606239324708 : (((False ∧ ((((((p1 → p5) → p1) ∨ True) → (p2 ∨ (p3 → True))) ∧ True) → p3)) ∨ (False ∨ True)) ∨ (((p5 → (True ∧ p5)) ∨ False) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40100617292822808496953997686 : (((((((True → (p3 ∨ p5)) ∧ (((p4 ∨ ((p2 ∧ p2) → (p2 ∧ (True ∧ p5)))) ∧ p5) ∨ p2)) → False) ∧ (p1 ∧ True)) ∧ p1) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116740885744836082962473875598 : (((p4 ∧ p2) ∨ ((((False ∧ p2) → True) → (((((p4 → p4) ∨ (p5 ∧ p1)) ∨ p5) ∧ True) ∨ p4)) → ((False ∧ p5) ∧ p1))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134102463923406182715048439576 : ((((p3 → (p2 → (((p5 ∨ p4) → True) → (p5 → (True → (p4 ∧ (((p5 ∨ p1) ∨ True) ∧ p4))))))) → p4) ∨ p4) ∨ (p1 ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228541027146404645632921547269 : ((p1 ∨ (p3 ∧ p5)) ∨ (((p5 ∨ p2) ∨ p1) ∨ (False ∨ (p4 ∨ ((False ∨ (False ∧ p4)) → ((True ∨ (p1 → (p3 → (p2 ∨ p2)))) ∧ p4)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695337724383951725519630910863 : (((((p4 ∧ (p4 ∨ (((False → p3) → (p5 ∧ p2)) → (False → p5)))) → p3) → (((p3 ∨ p3) ∨ (False ∧ False)) ∧ (p3 ∧ (False → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712422258563574957779546427108 : (((((p4 ∧ (p2 ∨ False)) ∧ (p2 ∧ p5)) ∨ ((p4 → (False → ((True ∨ (p2 → ((p4 ∨ p3) → False))) ∧ p2))) → (p5 → (p3 ∨ p5)))) ∨ p2) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219234050061629681407372565119 : ((p1 ∨ ((p2 ∨ p2) ∨ p1)) → ((p4 → (True → ((((p2 → p2) → p3) → (((p1 ∨ True) → p4) ∧ True)) → (False ∧ False)))) ∨ (False → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
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
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57905877985515965518801822890 : (((p4 ∨ (p1 ∨ p1)) → (((p3 ∨ (p4 → ((p4 → p5) ∧ ((p1 ∧ (p4 ∨ p3)) ∨ p1)))) ∨ ((p3 → (True ∨ True)) ∨ p3)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142833106520203849884372771659 : ((p3 ∨ (p5 → ((((False ∨ ((p3 → ((p2 → (False → (False ∨ False))) → (p4 ∧ p1))) ∨ p3)) ∧ p5) ∧ p1) ∧ True))) → ((p1 ∨ False) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719094453109587053256662150582 : ((((False ∧ ((p5 ∨ False) ∨ p4)) ∨ ((True ∧ ((p1 ∨ ((True → p4) → p4)) → ((True ∨ p5) → p4))) ∨ ((False → (p3 ∨ p5)) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118422435555226613669304166510 : ((p2 ∨ (False ∨ ((((p1 → ((p3 → False) ∧ (True ∨ p1))) → (p5 → (p4 ∨ True))) ∨ p1) ∧ (p1 ∨ ((p3 ∨ False) ∨ p2))))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76895755680501827690536103049 : ((((((p5 ∨ False) ∨ (p3 ∨ (True → True))) ∧ (p2 ∧ p3)) → ((p5 → ((p1 ∨ p4) ∨ p5)) ∧ ((False ∨ p3) → (p5 → p3)))) → False) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p5 ∨ False) ∨ (p3 ∨ (True → True))) ∧ (p2 ∧ p3)) → ((p5 → ((p1 ∨ p4) ∨ p5)) ∧ ((False ∨ p3) → (p5 → p3)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h6.left
        let h10 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h6.left
        let h15 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h6.left
        let h18 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
    -- Implications on the right can always be decomposed.
    intro h19
    -- Implications on the right can always be decomposed.
    intro h20
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h3.left
      let h24 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- Conjunctions on the left can always be decomposed.
          let h27 := h24.left
          let h28 := h24.right
          -- One of the premise coincides with the conclusion.
          exact h28
        case inr h29 =>
          -- False on the left can always be used.
          apply False.elim h29
      case inr h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- Conjunctions on the left can always be decomposed.
          let h32 := h24.left
          let h33 := h24.right
          -- One of the premise coincides with the conclusion.
          exact h33
        case inr h34 =>
          -- Conjunctions on the left can always be decomposed.
          let h35 := h24.left
          let h36 := h24.right
          -- One of the premise coincides with the conclusion.
          exact h36
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h37 := h1 h2
  -- False on the left can always be used.
  apply False.elim h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309314942752956716461163201149 : (p2 ∨ (((p2 ∧ (((True → (p1 ∧ (((p1 ∨ p5) ∨ p4) ∧ ((p5 ∨ p3) ∧ False)))) ∨ p3) → (p1 ∧ (p4 ∧ p3)))) ∨ True) ∨ (p5 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316378715207679174429741326972 : (p3 ∨ (False ∨ ((p5 → ((p4 ∧ ((False ∧ False) ∨ (((True ∧ p1) → p4) ∨ (p5 → (p3 ∧ p2))))) ∨ (p2 ∧ (False ∨ True)))) ∨ (p2 ∨ True)))) := by
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
theorem thm_5_vars_802397582505747954911120953171 : (((p2 → (False ∨ ((((p3 → p2) → p5) → p4) ∧ ((p1 ∧ p2) → ((p3 ∨ (p4 → p3)) ∧ ((((p1 ∧ p5) ∨ p3) ∧ True) → True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803683084977848055395070300526 : (((p3 → ((p4 ∨ ((p4 ∧ p4) → ((p3 → p4) → ((p3 → (p3 ∨ (((False ∧ (p5 ∨ p3)) ∧ p2) ∨ False))) ∧ (p3 → p2))))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307640268985465216280396091961 : (p1 ∨ (p1 → ((True → p4) ∨ (((p3 → p3) → ((False ∧ (p5 ∨ (p5 → (((p2 ∧ (p3 → (p3 ∨ p2))) ∨ p1) → p2)))) ∨ True)) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_458144704641488217557276951249 : ((((((True ∧ p1) ∨ p1) → ((p3 → ((p4 ∨ (p5 ∧ (p5 → p2))) → (p5 ∨ p1))) → p5)) ∨ ((p3 → p3) ∧ (p2 ∨ (False → False)))) ∧ True) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
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
theorem thm_5_vars_616552977850061300967418887625 : (((((((p3 → (False ∨ (p5 ∨ p3))) → (p2 ∨ p2)) ∨ True) ∧ (((p5 ∧ (p2 → (True → False))) ∨ (False → (p5 ∨ p4))) ∨ p5)) ∨ p4) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_51938400120950402369376344440 : (((((p4 ∧ ((p1 ∨ False) ∨ (p2 → True))) → p2) ∨ (((False ∧ p5) ∧ p2) ∨ p4)) ∨ (p3 ∨ ((False ∨ (p2 ∨ False)) → (p2 → p2)))) ∨ False) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689576981105439179644238277735 : ((((((((True → False) ∨ p2) → p1) → False) ∧ (False ∧ (((p3 → True) → p4) ∧ True))) ∨ (p1 ∨ (p4 ∨ (False ∨ ((p5 ∨ True) ∨ p1))))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_136256294111465990941499512056 : (((p4 → (p1 ∧ (p5 → (False → p1)))) ∨ ((p3 ∨ p3) ∧ (((p5 ∨ p2) → (p2 ∧ p1)) ∨ ((p5 ∨ True) ∧ False)))) ∨ ((True → False) → p4)) := by
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
theorem thm_5_vars_215707752618909943551983300316 : ((False ∨ ((p3 ∨ p2) → p1)) ∨ ((((True → (p2 ∨ (p5 ∧ p3))) → p3) ∧ (((((p5 ∧ True) ∧ p1) ∧ p3) → (p4 ∨ p4)) ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117534470498302658972261251042 : ((p2 ∧ ((((((True ∧ ((p5 → (p5 ∧ p5)) ∨ True)) ∨ False) → p4) ∧ ((p4 → p4) ∧ (p5 ∨ p5))) → p3) ∨ (True → False))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58946942090432004764904666526 : (((p2 ∧ True) ∨ (((((p1 ∧ p3) ∧ p3) ∧ True) ∧ ((p2 → ((p2 ∧ ((p4 ∧ p3) ∧ True)) ∨ True)) ∧ False)) ∧ (False → (p3 → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356012969920846193980471845748 : (p5 → ((((p1 → (p3 ∧ ((((p2 ∧ True) ∧ (True ∧ (p1 ∨ p1))) → p3) ∧ (p1 → False)))) → False) ∨ p1) ∨ (((True ∧ p5) ∧ p5) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103304139084240327597265250054 : (((p2 ∨ ((((p5 → p1) ∨ p3) → (p5 ∨ (((p1 → p2) ∨ True) → (p1 ∨ ((p1 ∧ p3) ∧ p3))))) ∨ (p3 ∧ p5))) ∨ True) ∧ (True ∨ p5)) := by
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
theorem thm_5_vars_45824441166999530567059940069 : (((p2 → (((((p2 ∨ (p5 → (True ∨ ((False ∨ (p5 ∨ p2)) ∨ True)))) → p1) → (p1 → p1)) ∧ (True → (p1 ∨ p3))) → True)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211291628195040901594505716913 : (((p5 ∧ p4) ∨ (p5 → p5)) ∧ ((p2 ∨ True) ∧ (True ∧ ((p2 ∧ (p1 ∧ ((((p2 → p1) → p4) → p1) → (p2 → p4)))) ∨ (True ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55207858592259078149942961014 : ((((p2 ∧ (True → True)) ∧ (p5 ∨ False)) ∨ (p2 ∨ (p4 ∨ ((p1 ∨ ((((p4 ∧ (p4 ∨ p1)) ∧ p5) ∧ p2) ∨ True)) → (p5 ∨ True))))) ∨ p5) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187034725173008823855701384401 : (((True ∧ p3) ∧ ((True ∧ (p5 ∧ (p3 → (p1 ∧ False)))) ∨ p2)) → (p2 ∨ (True ∧ (p3 ∧ ((False ∧ (p2 ∧ p3)) ∧ (True ∨ (p2 → False))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344748689067827987341193373054 : (p2 → (p3 → (True ∧ ((p1 ∧ p4) ∨ ((p5 ∨ ((p4 ∧ ((p3 ∨ (p1 ∧ p5)) → (True ∧ p4))) ∨ ((p3 ∧ False) → p1))) → (False ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
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
theorem thm_5_vars_322800844077861438910582525227 : (p5 ∨ ((((((p2 ∧ ((True → False) ∨ p2)) → p1) → (((p1 ∨ p5) ∨ p5) → (p4 → p1))) ∨ True) → (p2 ∧ (False ∧ (p5 → p5)))) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p2 ∧ ((True → False) ∨ p2)) → p1) → (((p1 ∨ p5) ∨ p5) → (p4 → p1))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208795453650879583413293347050 : ((p2 ∧ (True → ((False ∧ p4) ∧ True))) → (p1 ∧ ((p1 → (((p3 ∨ ((False ∨ p5) ∨ (p3 → (True ∧ (p5 → p5))))) ∨ p3) ∧ False)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58880547751677917324635705878 : (((False ∧ p1) ∨ ((True ∧ ((p4 ∨ p1) → (p5 ∧ p1))) → ((p5 ∧ p4) ∨ ((True ∧ (p1 ∨ (p1 ∨ (False ∨ False)))) → (p1 → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



