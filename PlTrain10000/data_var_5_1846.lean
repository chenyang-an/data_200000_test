variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637678597417987300038368019816 : (((((((p2 ∧ (False ∧ False)) → ((p3 → p2) ∧ True)) ∨ p5) → (((p3 ∨ ((p3 → False) → p2)) ∧ p5) ∧ (False ∧ (p5 ∨ True)))) → p3) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∧ (False ∧ False)) → ((p3 → p2) ∧ True)) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302807354421084503982434665791 : (False ∨ (p5 ∨ ((((p3 ∨ (((p5 ∨ False) ∨ p2) ∧ True)) → p1) ∧ ((p4 ∧ ((p2 ∧ p2) ∧ (p1 ∨ (True ∨ (p4 ∧ p5))))) ∨ False)) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h14 : (p3 ∨ (((p5 ∨ False) ∨ p2) ∧ True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h15 := h2 h14
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h19 : (p3 ∨ (((p5 ∨ False) ∨ p2) ∧ True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h20 := h2 h19
        -- One of the premise coincides with the conclusion.
        exact h20
  case inr h21 =>
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811150496833725838921165113597 : (((p5 → (p3 ∧ (((((p3 ∨ False) → p1) → (False ∧ (p3 ∨ (p3 → (False ∨ True))))) → ((True ∧ ((p2 ∧ p1) ∨ True)) → p2)) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802903796025441967891295707026 : (((p3 → ((((p5 ∨ False) ∧ (p5 ∨ ((((p5 → (p1 → ((((True ∨ p4) ∧ p2) → p4) ∨ p1))) → False) → False) ∨ p3))) ∧ p5) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753229763798227951277861391209 : (((False ∧ (((((False ∨ p5) ∨ ((((True ∨ p2) → True) ∧ p1) → p1)) ∧ (p2 → (False ∧ (p5 → True)))) → (p3 ∧ p3)) ∨ (p3 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601078570524772751939256610497 : ((((p1 ∧ (True ∧ (((p1 ∨ (((p3 ∧ (((p5 ∨ ((False ∨ p1) ∨ p3)) ∨ True) → p1)) ∧ (p4 ∧ p3)) ∧ p2)) → p1) ∧ p2))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117942541768096882256952982397 : ((p5 ∧ (p2 ∧ ((p4 ∧ (True → p4)) ∨ (p5 ∨ ((False → p5) → ((False ∨ p1) → ((((False ∨ p4) ∨ p4) ∨ False) → True))))))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738066319236023559580752907702 : ((((False ∧ False) ∨ ((((((True ∨ True) → p5) ∨ (((p4 ∧ p1) ∧ ((True ∨ p1) ∨ p2)) ∨ ((False ∨ p2) ∨ p2))) ∨ False) ∨ False) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20816772746166239134122567751 : (((((p4 ∧ (True → False)) → (p3 ∨ ((p1 ∨ p4) ∨ p2))) → p4) ∨ (False ∨ (((True ∨ p3) ∨ False) ∨ (False ∧ ((p5 ∧ p5) → p2))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593874569993227627702527885921 : ((((((((p2 ∨ (((p3 ∧ p4) ∨ (p5 → p4)) → (p4 ∨ p5))) ∧ p1) → (p2 → p2)) → p2) ∨ ((True ∧ p2) → (p1 → True))) ∧ True) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149121997182584415686506850170 : (((p1 ∧ p2) ∧ (((True ∨ ((False ∨ (True ∨ (p2 ∨ p4))) → (((p3 ∧ p3) ∧ p3) → p4))) → p5) ∨ p3)) ∨ (p3 → (True ∨ (True → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165293340940124407391197015444 : ((((p4 ∧ (True ∧ True)) ∧ (((True → (p1 → p4)) ∨ p1) ∧ (p5 → False))) → (p4 → p2)) ∨ ((((p3 ∧ p5) ∨ p4) → p3) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215102479686405785254909571685 : (((p1 → p3) → (False ∨ p1)) ∨ ((((p5 ∨ ((p1 ∧ ((((True → (False → p2)) ∨ p4) ∨ p2) ∨ (p1 ∨ False))) → True)) ∨ p5) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766831810319000438109789978720 : (((p4 ∧ (p4 ∨ ((((p4 ∨ (p4 → (p1 → ((p5 ∨ ((p1 ∨ p5) ∧ ((p5 ∨ (p2 ∨ p1)) → True))) → p1)))) → p5) → p1) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760136958223296329780046221566 : (((p2 ∧ (((True → False) ∨ p2) → (((p3 ∧ True) ∨ True) ∧ (((p2 → (p3 ∨ p4)) ∨ (p3 ∧ (p2 ∨ (p2 ∨ p4)))) → (p5 ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149575345927013270013688161507 : ((p2 ∧ (p1 → (((p2 ∨ ((p1 ∧ p4) ∨ ((p1 → (p4 ∨ (p2 ∨ True))) ∨ True))) ∧ p4) ∨ (True ∨ p2)))) ∨ ((p4 → p2) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666744383471484551894402500787 : ((((((False ∧ p3) → (((p5 ∧ False) ∧ False) ∧ (p1 → False))) → (((((p3 ∧ p3) → True) ∨ p1) ∧ p1) ∧ p5)) ∧ (p5 ∨ (p5 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112908362409859875562783892260 : ((((True ∨ p2) ∨ ((p2 ∧ (((False → ((((p2 ∧ p3) ∧ p2) ∨ False) ∨ p3)) → p3) → p3)) → ((p4 ∨ p1) → p5))) → p3) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615278643640012203438929754958 : (((((((False ∧ p2) ∧ (((p2 → p5) → (p1 ∨ p3)) ∧ ((True ∨ p4) ∨ p2))) ∧ p5) ∨ (False ∨ (p2 ∨ ((p4 → p3) ∧ False)))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803644862615401554874194405393 : (((p3 → ((p1 ∧ ((((((True ∧ p4) ∧ p2) ∧ (p1 → p5)) ∨ (True ∨ (True ∨ False))) → (p1 ∨ (p3 ∧ True))) ∧ (True ∧ p4))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52660425699412315036727200247 : (((p3 ∧ ((p4 ∨ True) → ((False → ((p5 → p1) → p5)) ∧ (p1 → False)))) ∨ ((p5 → p5) ∨ ((((p5 → True) ∧ False) → True) → p5))) ∨ p3) := by
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
theorem thm_5_vars_702755963900999258374757802645 : ((((((((p5 → p5) ∨ True) → False) → p2) → (False ∨ p4)) ∨ (((((p4 ∨ (p2 ∨ p1)) ∨ (p4 ∨ (True ∨ p5))) ∨ True) ∨ p1) ∨ False)) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214091134493963356043200591854 : ((((p4 ∧ p3) ∨ False) → False) ∨ ((((p1 ∨ ((((False ∨ p3) ∧ p1) ∧ p4) ∧ (p1 ∧ p4))) ∧ (p4 → (p4 → p2))) ∧ False) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689581739324435665930530428708 : ((((((p3 → (p4 ∧ p4)) → (p4 → p2)) ∧ (p3 ∧ (p4 → (p2 ∧ (True ∨ p2))))) ∨ (p4 ∨ (True ∨ ((False → p4) ∨ (p2 ∨ p2))))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118863409772728677669722042527 : ((True → ((((p2 → False) → p1) → p1) ∧ (False ∨ (((((p4 ∨ (False ∧ p2)) → p2) → p2) ∨ ((p1 ∧ False) ∧ p4)) ∧ True)))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792803079142420900645988732878 : (((True → ((p2 ∨ (True ∧ p3)) ∧ (p4 → (False ∨ (((p4 → (p2 ∧ (p3 ∧ (p2 → ((p5 ∨ p4) ∨ (p2 ∨ p1)))))) → p1) ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595678400355085342613495726878 : (((((p2 ∨ (p1 → (p4 ∨ (p1 → ((p4 → True) ∨ (p5 ∧ p1)))))) → ((p1 ∨ p3) ∨ ((p4 ∧ (p2 ∧ p1)) ∧ (p4 ∧ p1)))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753873950299231037897267703119 : (((False ∧ (((True ∧ (p2 → ((False → p4) → False))) ∧ p5) ∨ ((p4 ∧ (p4 ∨ (((p3 ∨ p5) ∧ (False ∨ False)) → True))) → (False ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_823165506577363835937169235726 : ((((((((True ∨ True) ∨ p3) → False) ∨ p5) ∧ (p2 → ((p2 ∧ (p3 → ((True ∧ (p1 ∨ ((p4 ∧ p1) ∨ p4))) ∧ True))) ∨ False))) ∧ p2) → p5) ∧ True) := by
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
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : ((True ∨ True) ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608739223522833682144951041040 : (((((((p1 → (((True ∧ p3) ∧ ((p5 ∨ p5) ∧ ((False ∨ (False ∨ p4)) → True))) ∧ p3)) ∧ p2) ∧ (p4 ∧ (p3 → p1))) ∨ True) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_152860552567659824565465151634 : (((p5 → p1) → (True → ((p1 → (p4 ∨ p2)) → ((((((True ∨ p4) ∧ False) ∨ p1) → p4) → p3) → True)))) → ((False ∨ p2) → (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_473629359184141129343046684998 : (((((p3 → True) ∧ (p2 ∧ ((p4 ∨ p3) ∧ (True → (True ∧ p5))))) → ((False → (False → (p1 ∧ True))) ∧ ((p1 ∧ False) ∨ (p4 → p5)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
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
    -- Implications on the right can always be decomposed.
    intro h11
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h13 := h9 h12
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h17 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h18 := h9 h17
    -- We need to get the right conjuct of h18 based on <expert-advice>.
    let h19 := h18.right
    -- One of the premise coincides with the conclusion.
    exact h19
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67316859488375850667690763660 : ((p1 → ((p4 ∨ (p3 → (((p4 ∧ p2) ∨ (p4 → p5)) ∨ ((p3 ∧ p3) ∧ (p1 → ((((p4 → p2) ∧ False) ∧ p2) ∨ p3)))))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41262334434267691159682516955 : (((((p5 ∧ p4) ∨ ((p5 ∧ (p1 ∨ ((False → True) ∧ (p4 ∨ (p4 ∨ (p2 → False)))))) ∨ p5)) ∨ ((p4 → (p4 ∧ False)) ∧ p4)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18118050897272654720973901124 : (((p2 → ((((p1 ∧ p1) → (((False ∨ (False ∧ True)) ∨ (p5 ∧ True)) ∧ p5)) ∧ p1) ∨ (p5 → p5))) ∨ (((True → p3) ∧ True) ∨ False)) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40698360378781707283837458711 : ((((((p4 → ((p2 ∧ (p5 → (((p1 → p4) ∨ p5) → p3))) ∨ False)) ∧ p3) → ((p4 ∨ (p1 ∨ p2)) → (p2 → p1))) → p1) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241659194996465096357783820552 : ((False → p5) ∧ ((((p3 → False) ∧ (((False ∨ p1) → p2) → p3)) ∨ (p1 → (False → p3))) ∨ (((((p4 → p1) ∨ p4) → False) ∨ p3) ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217402456950058048794887322030 : (((False → (p5 ∧ p2)) ∨ p5) → ((((True ∨ False) → False) ∨ (p2 ∧ ((p3 → p2) → (p3 → p2)))) ∨ (p5 ∨ (False → ((p3 ∧ p5) ∧ False))))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174942774613411801977886381424 : (((p4 → p3) → (p1 ∧ ((p5 ∧ ((p4 ∧ (p5 ∨ False)) ∨ p3)) ∧ (True ∧ p2)))) → (((((True → p2) ∧ (p2 ∧ p1)) ∧ p3) ∧ p5) → p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184860849907694545789710517338 : ((((p4 ∧ p3) ∨ p5) ∧ ((False ∧ ((p5 → False) → p1)) ∧ p2)) ∨ ((((((p3 → (p2 ∧ (p3 ∧ p3))) ∨ False) ∨ p2) ∧ p4) ∧ p3) → p4)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341721748472402788094617184749 : (p2 → ((((p2 ∨ p2) ∧ ((p1 → p3) ∨ p5)) ∨ (p2 ∧ (((False → (p3 ∧ p3)) ∧ ((p5 → p3) ∨ (p1 ∨ p2))) → p5))) ∨ (True ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665862711650539085940483224369 : (((((((p2 → ((True ∧ (p5 ∨ True)) ∨ ((p2 ∧ (p2 ∧ True)) → p3))) ∧ True) ∨ ((p1 → True) ∧ p1)) → False) ∧ (p5 → (p3 ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338760860289750243693197225376 : (p1 → ((False ∧ p3) ∨ ((((True ∨ p2) ∧ (((p4 ∨ ((p1 → (p3 ∧ (p3 ∧ (p2 → p2)))) ∧ False)) ∧ p3) ∧ (False ∨ True))) ∨ p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115856341394575505167622720722 : (((p5 ∨ (False ∧ (p5 ∧ p3))) ∧ ((((p1 ∨ p2) → p2) ∧ (p2 → (p2 ∨ ((True ∧ True) ∨ p4)))) ∧ ((p2 ∨ p1) → p3))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725700207251981551906223660725 : (((((False ∨ p1) ∧ p4) ∨ (((((p5 ∧ (p1 → p1)) ∧ p5) ∨ (p2 → ((p4 → False) ∧ (p3 ∧ p2)))) ∨ True) ∨ (p3 ∨ (p2 ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208578496690948828477397535716 : (((False → False) → ((p5 ∧ p3) ∨ p5)) → (((((True → ((False ∨ p2) ∨ False)) ∧ p4) ∨ p1) ∧ (p3 ∧ True)) ∨ ((p1 ∨ True) ∨ (p2 ∨ p5)))) := by
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
theorem thm_5_vars_172676242978506569898288954226 : (((p5 → False) ∧ (False ∨ (p1 ∨ (((p3 → p3) ∧ (False ∨ True)) ∧ (False ∧ p3))))) ∨ (p1 ∨ (((p1 → ((False → False) ∧ p1)) ∧ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251840041607310055389211207710 : ((p3 → p5) ∨ (((p5 ∨ (p3 ∧ (p4 → ((p3 ∨ p1) ∨ (p2 → (((p2 → (p5 → p4)) → ((p3 ∨ True) ∧ p4)) ∧ True)))))) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_240475723399741846752755443725 : ((p5 ∨ True) ∧ (p4 → (((((p2 ∨ (p2 ∨ p5)) ∨ p2) ∨ (p1 ∨ p5)) ∧ ((p5 ∨ p4) ∨ p5)) ∨ (((False → p5) → (True ∧ p1)) → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_215214967373271672738645905747 : ((True ∧ (p4 → (p2 → p3))) ∨ (((((p4 ∧ (p3 ∧ p5)) → True) → False) ∧ (True → (True ∧ p3))) → (((p5 → (p4 → False)) ∧ p4) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((p4 ∧ (p3 ∧ p5)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h11 : ((p4 ∧ (p3 ∧ p5)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h12
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h13 := h9 h11
  -- False on the left can always be used.
  apply False.elim h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
  have h16 : ((p4 ∧ (p3 ∧ p5)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h17
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h14, we can now drive its conclusion.
  let h18 := h14 h16
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720343332161234174161196577331 : ((((((p5 ∨ p1) ∨ p5) ∨ False) → (p5 → ((p4 → ((p2 ∨ ((True ∨ (p5 ∧ (True → False))) → (p2 ∧ p1))) ∧ (p4 → p2))) ∨ True))) ∨ p4) ∧ True) := by
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
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185463276825065571226006175130 : ((p1 ∨ (((((False ∨ p5) ∨ p2) ∨ True) → (False ∨ p4)) → p4)) ∨ ((p1 ∧ (p3 ∧ (p4 ∨ (((p4 → p2) ∨ (p1 → p4)) → False)))) → p3)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175963530965960252892995242259 : (((p5 ∨ ((p5 ∨ ((p4 ∧ p2) ∧ (p3 ∧ False))) ∨ (p4 → p5))) ∨ True) ∧ (False → (((((p3 ∨ False) ∧ (p2 ∧ True)) → p4) ∨ p2) ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172969065046865991113850847145 : ((p4 ∧ (((p3 → ((p3 ∨ p3) ∨ p2)) ∧ p5) → (p2 ∧ ((False → p1) ∨ p2)))) ∨ ((p1 ∨ (True → (p2 → p2))) ∧ (p1 → (p1 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214010909754797190027549432400 : ((((p3 ∧ p4) ∧ p1) → False) ∨ ((False ∧ (((p1 → (p4 ∧ p5)) → (p5 → p1)) → ((((p5 → p4) → False) → (p5 ∨ p1)) ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265645762240562484039781355461 : (True ∧ (p2 ∨ ((((True → (p5 ∨ ((((p4 → True) ∧ (p2 ∧ p1)) ∨ True) → True))) → p5) ∨ ((p5 ∨ (p3 → True)) ∨ p4)) ∨ (p3 ∧ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147587803811378360010878261433 : (((((((True ∨ p1) ∨ True) ∧ (((p1 ∧ (False ∧ p3)) → (p5 → True)) ∨ (False ∨ p5))) ∧ p2) ∨ p1) → p5) ∨ (p5 ∨ (p4 ∨ (p5 → True)))) := by
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
theorem thm_5_vars_923580819746514481362216784399 : (((((((p2 ∨ (p3 → p3)) ∨ p5) → True) → ((p2 ∧ p2) ∧ False)) ∧ (p5 → ((p1 ∨ ((p5 ∧ False) → False)) ∧ (True → (p3 ∧ p2))))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p2 ∨ (p3 → p3)) ∨ p5) → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_23991643994209600725902385094 : ((((p1 ∧ (p5 → p4)) ∨ p1) → ((((p4 → p3) → False) ∧ False) ∨ (True ∧ ((False ∧ (p1 ∨ p1)) → ((p5 ∧ (True ∨ p5)) ∨ p4))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112379391794315692721950839491 : (((((False → (p1 ∧ (((False ∧ (p1 ∧ ((p1 ∧ (True ∨ p1)) ∨ p3))) → p1) → p4))) ∨ ((True → False) → True)) ∧ True) → p5) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67900699345499318770604547758 : ((p2 → ((p3 → ((p1 → ((False → (p5 ∧ p2)) ∧ p3)) ∧ (((True ∨ p1) → False) → False))) → ((False ∧ p3) ∧ ((False ∧ p3) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192173464302535278591701512692 : ((((((p1 ∨ (p2 → p2)) ∧ p2) ∧ p3) ∨ p2) ∧ p4) → ((((p2 → (True ∧ ((True ∨ True) ∧ p1))) ∨ (False ∨ (True ∨ False))) ∨ p5) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299183769322241875046623520222 : (False ∨ ((((p5 ∨ (True ∨ p2)) ∧ ((((p1 ∧ (((((p2 ∧ p4) ∨ p5) ∨ p3) ∨ False) ∨ p2)) ∧ (p3 → False)) ∨ True) ∨ p3)) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348892667937623158709419819029 : (p3 → (p2 ∨ (p1 ∨ ((((p4 → (((p5 ∨ ((p2 → p3) ∨ False)) → p1) ∧ (True ∨ p4))) → (((True → p4) ∧ p2) ∧ p2)) ∧ True) ∨ p3)))) := by
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
theorem thm_5_vars_302544579419714588699032202269 : (False ∨ (False ∨ (p5 ∨ (p4 ∨ (((False → ((p4 → (p4 ∧ ((True → p3) → ((p1 ∨ p3) ∧ (p1 → (False ∨ False)))))) ∧ p5)) → p5) ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205936236211764038930785308536 : ((False ∧ ((True ∧ p4) ∨ (True ∧ p4))) ∨ (((p1 ∧ p5) → p4) ∨ ((False ∨ True) ∨ ((((p2 → (True → p4)) ∧ p4) ∧ (p5 ∨ True)) → True)))) := by
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
theorem thm_5_vars_207599636485909405264623409614 : (((((p5 ∧ p3) ∨ p5) → p5) → p5) → ((((p5 ∧ p4) ∧ (((p3 → (p1 ∧ p5)) ∨ p1) ∨ p5)) ∨ p4) ∨ (((p2 ∧ p4) ∧ p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156828652688403102808097278435 : (((True → ((((((p2 ∧ (p5 ∨ p5)) ∧ True) ∧ p5) ∧ (p5 ∧ (False → p5))) → p4) → p5)) ∧ p2) ∨ ((p4 ∨ ((p4 ∨ p1) ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55373792653737201943403936797 : ((((((p5 ∧ p2) ∨ True) ∨ p5) ∧ p2) → (False ∧ ((((p4 ∨ p5) ∨ (((True ∨ p3) ∨ p2) → (p3 → (p5 ∨ False)))) ∨ p4) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180530502268822266375906794216 : ((((p4 ∨ (p4 ∨ (True ∨ p2))) ∧ (p2 → p4)) ∨ ((False ∨ p2) ∨ p3)) → ((p1 ∧ (((p1 ∨ p5) → (p2 → (p3 → True))) → False)) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h9 : ((p1 ∨ p5) → (p2 → (p3 → True))) := by
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- Implications on the right can always be decomposed.
        intro h12
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h13 := h4 h9
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h16 : ((p1 ∨ p5) → (p2 → (p3 → True))) := by
          -- Implications on the right can always be decomposed.
          intro h17
          -- Implications on the right can always be decomposed.
          intro h18
          -- Implications on the right can always be decomposed.
          intro h19
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h20 := h4 h16
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h23 : ((p1 ∨ p5) → (p2 → (p3 → True))) := by
            -- Implications on the right can always be decomposed.
            intro h24
            -- Implications on the right can always be decomposed.
            intro h25
            -- Implications on the right can always be decomposed.
            intro h26
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h27 := h4 h23
          -- False on the left can always be used.
          apply False.elim h27
        case inr h28 =>
          -- One of the premise coincides with the conclusion.
          exact h28
  case inr h29 =>
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- False on the left can always be used.
        apply False.elim h31
      case inr h32 =>
        -- One of the premise coincides with the conclusion.
        exact h32
    case inr h33 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h34 : ((p1 ∨ p5) → (p2 → (p3 → True))) := by
        -- Implications on the right can always be decomposed.
        intro h35
        -- Implications on the right can always be decomposed.
        intro h36
        -- Implications on the right can always be decomposed.
        intro h37
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h38 := h4 h34
      -- False on the left can always be used.
      apply False.elim h38



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77914315288971507956434407809 : (((p2 ∨ (((p4 ∧ True) → (((False → ((p4 ∧ ((p3 ∧ (True → p4)) → p3)) ∧ p4)) ∨ p1) ∧ (p2 ∧ p1))) ∨ (p4 ∨ True))) → p1) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ (((p4 ∧ True) → (((False → ((p4 ∧ ((p3 ∧ (True → p4)) → p3)) ∧ p4)) ∨ p1) ∧ (p2 ∧ p1))) ∨ (p4 ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
theorem thm_5_vars_324718559665994694029962351741 : (p5 ∨ (((p2 → True) ∨ p2) → ((p4 ∨ ((p3 ∧ False) ∨ (p2 ∨ ((p5 ∧ ((p4 ∨ p5) → p3)) → ((p5 ∨ (True ∧ p2)) ∨ p1))))) ∨ p3))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603173943455248432169363205038 : ((((p2 ∨ (((p3 → p4) → (False ∨ ((((p2 ∧ p4) → p5) ∨ p3) ∧ (((p3 ∧ True) ∧ (p4 ∧ p4)) ∨ False)))) ∨ (p4 → p5))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714351004857617621242047387578 : (((((p2 ∨ (True ∨ True)) ∨ (False → p2)) → ((p3 ∨ p4) ∧ ((((False → p5) ∨ (True ∨ True)) ∨ ((False ∨ p1) ∧ p3)) ∧ (True ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2592678689478788692673943865 : (((True ∨ p1) → ((p5 → False) ∧ (p3 ∧ p5))) → ((p5 → p5) → (((p5 → ((((False ∧ p3) → p2) ∨ p1) → p1)) ∨ False) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : (True ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h6
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230716129440977224601284606869 : (((p4 → p5) ∧ p4) → ((((False ∨ (p5 ∨ (p3 → p4))) ∧ (((p3 → p4) ∨ False) ∧ (True ∧ (p4 → False)))) ∧ (True → False)) ∨ (True ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205148963812709124858221218532 : (((True ∧ (p4 ∧ p4)) ∧ (p2 ∨ p3)) ∨ (((p2 ∨ ((False ∨ ((p1 → ((p5 → True) → False)) → True)) ∧ (p5 → (p3 ∨ True)))) → False) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ ((False ∨ ((p1 → ((p5 → True) → False)) → True)) ∧ (p5 → (p3 ∨ True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178483052902381759452140862754 : ((((((False → False) ∨ True) ∧ p5) ∨ (False ∧ p1)) ∨ ((False ∧ False) ∧ False)) ∨ ((((p3 ∨ p1) → (p5 → ((p3 ∧ p2) ∧ p3))) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54551383797775868071354301188 : (((p1 ∧ (((p2 → p5) ∧ p1) → (p3 ∧ p4))) ∨ (False ∨ (((True ∧ (p1 → (True ∨ (False ∨ (p3 ∧ True))))) → (True ∨ p5)) ∧ True))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208203757024819718531388399087 : (((False → (True ∧ p4)) → (p5 ∧ False)) → ((p2 ∧ (p4 ∧ (p3 ∧ (p3 ∨ (((True ∨ (p4 → (p5 ∧ p1))) ∨ p5) → p2))))) ∧ (p1 → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → (True ∧ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (False → (True ∧ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : (False → (True ∧ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- False on the left can always be used.
    apply False.elim h11
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h10
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- False on the left can always be used.
  apply False.elim h13
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h14 : (False → (True ∧ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- False on the left can always be used.
    apply False.elim h15
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h14
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- False on the left can always be used.
  apply False.elim h17
  -- Implications on the right can always be decomposed.
  intro h18
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h19 : (False → (True ∧ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h20
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- False on the left can always be used.
    apply False.elim h20
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h21 := h1 h19
  -- We need to get the right conjuct of h21 based on <expert-advice>.
  let h22 := h21.right
  -- False on the left can always be used.
  apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165791348315602196537776252169 : (((p3 → ((p4 ∧ p2) → p1)) → (((True ∧ (False ∧ True)) → (p4 ∧ False)) ∧ (False ∧ p3))) ∨ ((((p4 ∧ p2) → (p3 → p2)) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180698381090516927217844694328 : (((((p3 → p5) → p2) ∧ p5) ∧ (True → ((p3 ∧ (p5 ∧ p3)) → True))) → ((((p3 → p1) → (((False ∨ p4) → p3) → p2)) ∧ p2) → p2)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765106958765238617467298356564 : (((p4 ∧ ((((((p3 ∨ (p1 → (True → False))) → (p1 → p2)) → ((True ∧ p4) ∧ (p4 → (False → True)))) ∨ p5) ∧ False) ∨ (p4 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180103937974413804795091672843 : (((((((p1 ∨ p2) → True) ∧ ((False → p5) → p5)) ∧ True) ∨ p4) → True) → (((((p4 ∧ p4) → (p2 ∨ False)) ∨ (p2 ∨ p3)) ∨ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135842226379511148340885999382 : (((p4 ∧ (((p4 → p1) ∧ (True ∨ (False ∧ False))) ∨ (p3 ∧ True))) ∧ ((p5 ∧ p3) ∨ (True ∧ ((p4 ∧ p3) ∨ p4)))) ∨ ((False → p4) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233559185689591113015554062089 : ((p1 ∨ (False → p1)) → (((p1 ∨ (p4 → (p5 ∧ False))) → (False ∧ p3)) ∨ ((p4 ∧ p4) → (p4 ∨ (False ∨ (p1 ∨ (p3 ∧ (p4 → False)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21764506694349487590576313693 : (((p1 ∨ (((p5 → p4) ∧ ((True → p4) ∧ p3)) ∧ True)) → (((p4 ∧ p3) → ((p2 ∨ (p1 ∧ p5)) ∨ p3)) ∨ (p4 → (p2 → False)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_836797018775983502276099872700 : (((((((False ∧ p4) ∧ ((p2 → (((p4 ∨ (True → (True ∨ (p4 → (p3 ∨ p5))))) ∨ p2) ∧ False)) ∨ (False ∨ p3))) ∨ True) → False) ∨ False) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (((False ∧ p4) ∧ ((p2 → (((p4 ∨ (True → (True ∨ (p4 → (p3 ∨ p5))))) ∨ p2) ∧ False)) ∨ (False ∨ p3))) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55863245718199323016802782866 : (((p4 ∧ (p1 → (False ∧ p3))) ∧ (p4 ∨ ((p1 ∧ ((((p1 ∨ False) ∧ p2) ∧ ((False ∨ ((True ∧ p2) ∧ True)) ∨ p5)) ∧ p2)) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162389429557068334966720145322 : ((((((((p5 → p4) ∧ False) ∨ p5) ∨ p3) ∨ ((p5 ∨ p3) ∨ p2)) ∨ (p5 → p5)) ∨ p5) ∧ ((p4 → p4) ∨ (p1 ∧ ((False ∨ True) ∨ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306009803227112926437560794847 : (p1 ∨ ((False ∧ ((p4 ∧ False) ∨ False)) ∨ ((True ∨ ((((p1 ∨ ((p3 ∧ ((False ∧ (p5 → p5)) ∧ p4)) ∧ p4)) ∧ p1) ∧ p4) ∧ p3)) ∨ p4))) := by
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
theorem thm_5_vars_59313224165263501569988543427 : (((p4 ∨ p1) ∨ (((((True ∧ (p2 → p5)) ∨ (False ∨ p3)) → True) → False) → ((p1 ∧ p1) ∧ ((False ∨ ((True ∧ True) ∧ p4)) → False)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True ∧ (p2 → p5)) ∨ (False ∨ p3)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (((True ∧ (p2 → p5)) ∨ (False ∨ p3)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- False on the left can always be used.
  apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h15 : (((True ∧ (p2 → p5)) ∨ (False ∨ p3)) → True) := by
      -- Implications on the right can always be decomposed.
      intro h16
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h17 := h1 h15
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218282715724595135861278697945 : (((p3 ∨ False) ∨ (p4 ∧ p3)) → (((p4 ∧ p1) ∧ ((p1 ∨ ((p4 ∧ False) ∧ False)) ∧ (False ∧ (True → False)))) ∨ ((False → (p4 ∧ p1)) ∨ p5))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h4
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h9
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623051975325093845862585639938 : ((((p5 ∧ (p3 ∨ ((p2 → (((p4 ∨ p4) → (p4 ∧ ((p1 ∨ ((p3 → p2) → (p3 ∧ p1))) ∨ (True ∨ False)))) ∧ False)) ∨ p2))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_134905968091040422415051649639 : (((((p3 ∨ (p2 ∧ p5)) ∧ ((((p2 ∨ True) → True) → p4) → (((p3 ∧ True) ∧ True) ∨ p5))) ∧ p5) ∧ (False ∨ False)) ∨ (True ∧ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307506755460019913778214321958 : (p1 ∨ (True → (((p5 → (True ∧ p3)) → (False ∨ (p2 ∨ (p2 ∧ (p3 → p5))))) ∨ ((False → (((p5 ∨ True) ∨ False) ∨ p4)) → (True ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136490338989330432641484551609 : ((((p1 ∧ True) → p5) ∧ ((p2 → ((p5 → p3) ∨ ((True ∧ p3) ∨ p5))) → (((False → True) ∨ p1) ∧ (p2 ∨ p1)))) ∨ ((p2 ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731583374354052864148979193461 : ((((p1 → (False ∧ False)) → ((True ∧ (p4 ∧ (((False → p4) ∧ (p4 ∨ (False ∧ (p4 ∨ p1)))) ∧ (p2 ∨ ((True ∨ p1) ∨ False))))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112876687186557361855106088931 : ((((p5 ∨ (p4 → p2)) → ((False → (((p3 → (p1 ∧ ((p1 ∨ False) ∨ (p4 ∧ (True → True))))) ∧ p5) ∧ False)) ∨ False)) → False) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51280298683056011260016866532 : (((p1 ∧ (p2 ∧ (p4 → (False ∨ (p5 ∧ ((p4 → ((p4 → (p2 ∨ p3)) ∧ p1)) ∨ p3)))))) ∨ ((p2 → True) ∨ ((p2 ∨ False) ∨ p5))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



