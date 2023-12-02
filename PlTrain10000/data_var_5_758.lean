variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168311558107786049434065981333 : (((p5 ∨ p4) ∧ (((((p4 → True) ∨ (p2 ∧ False)) ∧ (p5 → (p5 ∧ p5))) → False) ∧ p2)) → ((False ∨ False) ∨ (((p2 → p3) → p1) ∨ p2))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710727804038808081603821088954 : ((((((p3 ∧ p1) ∨ p3) → (p2 → p1)) ∧ (p2 ∨ ((False ∧ p5) ∨ (((p5 ∨ (p1 ∧ p2)) ∧ ((p4 → p5) → (False → False))) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251295705433017764479844960720 : ((p2 → p3) ∨ (((((p1 ∧ p4) → False) ∧ p1) ∨ (p5 → ((p5 ∨ p4) ∧ (((p1 ∧ (p4 ∨ p1)) ∨ (p1 → p5)) ∨ (False ∧ p5))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702946050723361633006327956384 : ((((((p5 ∨ False) ∧ p4) ∨ (False ∧ ((p3 → p3) ∨ True))) ∨ ((p2 ∨ False) → ((p5 ∧ (p5 → (p4 ∧ ((False → True) ∧ p5)))) ∨ True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44576236257108946827160190026 : (((((((True ∨ (p2 ∨ False)) → False) → False) → p3) ∨ (p3 ∨ (((((p1 ∧ ((p3 ∧ p2) → p1)) ∨ p5) ∧ p5) → p5) ∨ p4))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134118847614344948983667798090 : ((((((((p4 → p4) → p5) → (((p1 ∨ (p1 ∧ p3)) → p3) ∨ (True ∨ p5))) → True) → p3) ∨ (False → True)) ∨ p4) ∨ (p4 ∧ (p4 → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53087675367865889125724455316 : (((False ∨ (p1 ∨ ((p1 → p2) ∧ ((p4 → (True → p1)) → p4)))) ∧ (False → ((((p3 → (p3 ∧ p1)) → (p1 ∨ p2)) → p4) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112743197181437414285723230379 : (((((p2 ∧ (p4 → p2)) → ((p5 ∧ False) → ((p2 → p3) ∨ p5))) ∨ (p3 ∧ (((True ∨ True) → p4) ∧ (True ∨ True)))) → p2) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125071889271885247341631533025 : (((True ∨ (p5 ∧ True)) ∧ ((p4 → ((p4 ∨ (p3 ∧ (p1 ∨ p3))) ∨ (p4 → (p4 → ((p3 ∧ p2) ∧ (p2 ∨ p2)))))) → p4)) → (p2 ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (p4 → ((p4 ∨ (p3 ∧ (p1 ∨ p3))) ∨ (p4 → (p4 → ((p3 ∧ p2) ∧ (p2 ∨ p2)))))) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : (p4 → ((p4 ∨ (p3 ∧ (p1 ∨ p3))) ∨ (p4 → (p4 → ((p3 ∧ p2) ∧ (p2 ∨ p2)))))) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762222161949066583130433363268 : (((p3 ∧ ((((((((True ∧ False) → (p1 ∧ False)) ∧ p5) ∨ (p2 ∧ False)) ∨ ((p4 ∧ p2) ∧ (False → p1))) ∧ p4) → p5) → (p3 ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54468060663241160414981743094 : ((((((False ∨ p2) ∧ True) ∨ p1) ∧ (p3 → False)) ∨ (((True ∧ (p3 → False)) ∨ ((p2 → ((p4 → False) ∨ (p1 ∨ p4))) → p3)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168200228949799828670521738896 : ((((p3 → p1) ∨ p1) ∨ ((((True ∧ ((False ∨ (True ∨ p1)) ∧ p2)) ∧ False) → p3) → False)) → (((p2 ∧ True) → ((p1 ∨ p4) ∨ p5)) ∨ True)) := by
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
theorem thm_5_vars_175166091162036389594058117366 : ((True ∨ ((((p4 ∨ True) → ((p5 ∨ p1) ∨ False)) ∧ (p3 → p2)) ∧ (p5 → p4))) → (((p2 ∧ (True → p1)) → True) ∧ (p2 ∨ (False → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347094187645305814688336321644 : (p3 → ((((((((p5 → False) ∧ (p2 → p5)) ∨ p2) → False) → p2) ∧ False) ∧ False) ∨ (True ∧ (p4 ∨ (((p5 → False) → (p5 → p3)) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327110953695075005105203056522 : (True → (((p4 ∨ p2) ∨ ((p1 → p3) → ((p4 → ((((p5 → p1) → p3) → (False → p3)) ∨ p5)) → (p3 ∨ ((p1 ∧ p1) → p1))))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113673250944821716983292644449 : (((((p1 ∧ (p3 → p1)) ∧ (p3 ∧ ((p3 ∧ p5) → ((p1 ∨ p1) ∧ (True → ((True ∧ p4) ∧ False)))))) ∨ p4) → (False ∧ True)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261032284530158396471019045721 : ((p4 → p2) → ((((True ∧ ((p2 ∨ ((p2 → p1) → (p3 ∨ p2))) ∨ p1)) → p3) ∨ p3) → (p2 → (p3 → ((p2 → (p1 ∨ True)) ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h2
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251841340434074793332899353672 : ((p3 → p5) ∨ (((((p3 → ((p5 → False) ∨ ((False → p1) ∧ p2))) → p2) ∧ ((True ∧ True) ∧ p3)) ∧ ((p2 ∨ p5) ∨ (p1 ∧ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178882143711435494250998139685 : (((p3 ∧ p1) ∧ ((p2 → p1) → ((((p2 ∧ p2) → False) → p3) ∧ True))) ∨ (p5 → ((((p2 ∨ (p4 → (True → p1))) ∧ False) ∨ p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185241262206908864492124433763 : ((False ∧ (p3 ∨ ((False ∨ p4) ∧ (True → (p4 ∧ (p5 → p1)))))) ∨ (p2 → ((((((p1 ∨ p3) ∨ p1) ∨ p5) → (p4 → p2)) ∨ False) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h7 =>
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167996482397964328565594345147 : (((p5 ∨ (((p5 ∨ p5) → True) ∨ p3)) ∧ ((p3 ∧ (p3 ∧ (p1 ∧ p4))) → (False → p3))) → (p2 ∨ (p2 ∨ (p3 → ((p1 → p3) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137698111756206692840585632536 : ((p1 ∨ ((True → ((p5 → (p4 ∨ False)) ∧ (((((p5 ∧ p4) → p1) ∨ (False ∧ p2)) → p3) → p4))) ∨ (True ∧ p4))) ∨ (p4 ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324918517935650110838457524797 : (p5 ∨ ((p5 ∧ p1) ∨ (((p3 ∨ p3) ∨ (True ∨ (p2 ∨ (p4 ∧ (True ∧ (p4 → True)))))) ∧ (((p1 ∨ (p1 → p3)) → True) ∨ (p5 ∧ True))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606596612286733907628902784350 : (((((((False ∨ p1) ∨ ((p3 → ((p2 ∧ ((p3 ∨ (True ∨ ((p4 → p1) ∨ p2))) → p2)) ∨ (True ∧ p2))) ∧ p4)) → p2) ∧ p4) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329165500837735185956847760732 : (True → (((True ∨ True) ∨ (p5 ∧ p2)) → (((p4 ∧ (True ∧ True)) ∨ p1) ∨ ((((False ∨ (p2 ∧ (p3 ∧ p2))) ∧ (p5 ∧ p4)) ∧ True) → p3)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Conjunctions on the left can always be decomposed.
        let h16 := h9.left
        let h17 := h9.right
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h20.left
      let h23 := h20.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h24 =>
        -- False on the left can always be used.
        apply False.elim h24
      case inr h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- Conjunctions on the left can always be decomposed.
        let h30 := h23.left
        let h31 := h23.right
        -- One of the premise coincides with the conclusion.
        exact h28
  case inr h32 =>
    -- Conjunctions on the left can always be decomposed.
    let h33 := h32.left
    let h34 := h32.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h35
    -- Conjunctions on the left can always be decomposed.
    let h36 := h35.left
    let h37 := h35.right
    -- Conjunctions on the left can always be decomposed.
    let h38 := h36.left
    let h39 := h36.right
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h40 =>
      -- False on the left can always be used.
      apply False.elim h40
    case inr h41 =>
      -- Conjunctions on the left can always be decomposed.
      let h42 := h41.left
      let h43 := h41.right
      -- Conjunctions on the left can always be decomposed.
      let h44 := h43.left
      let h45 := h43.right
      -- Conjunctions on the left can always be decomposed.
      let h46 := h39.left
      let h47 := h39.right
      -- One of the premise coincides with the conclusion.
      exact h44



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322380669150207427999377814872 : (p5 ∨ (((((True ∨ p4) → ((p2 ∧ p5) ∨ ((False ∨ p3) ∧ (p3 → True)))) ∧ (True ∧ p4)) ∧ (p2 ∨ (((False ∨ p3) ∨ False) → p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149136826080879778924868537171 : (((p4 ∧ p4) ∧ ((p4 → ((p2 ∧ (((p5 → False) ∨ p4) ∨ p3)) ∧ p4)) ∨ ((False ∨ (p4 → p1)) → p2))) ∨ (True ∨ ((p4 ∧ p1) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40561101258412431856170953655 : ((((p2 → (False ∨ ((p5 ∧ ((((True ∧ p1) → p3) ∨ (True → p4)) ∨ p1)) ∨ (((p3 ∧ p1) ∧ (p3 → p1)) ∨ p3)))) ∨ True) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698628321987473113564681885896 : ((((((p1 ∧ p1) ∨ p1) ∨ (p1 ∧ (((p2 ∧ p4) ∨ True) ∧ True))) ∨ (((p4 ∧ ((True ∧ p1) ∨ p3)) ∨ (p4 ∨ True)) ∨ (p4 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157981745049844835766704228290 : ((((p3 → (p1 → (p3 ∨ (p2 → p1)))) ∧ p1) → (((p2 ∨ p5) ∨ p4) → ((p5 ∧ p1) ∧ p5))) ∨ (p2 ∨ ((p5 ∧ p1) ∨ (p4 ∨ True)))) := by
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
theorem thm_5_vars_720948502085988997586767169777 : (((((p2 ∨ p4) ∧ (p2 ∧ p4)) → ((p3 ∨ ((p3 → p3) ∨ (((True ∧ True) ∨ p2) ∧ False))) ∧ (((p3 → p2) ∨ True) → (p1 ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619631674657500368963004550869 : (((((p2 ∧ p3) ∧ ((p4 ∨ (p2 ∨ (((p4 ∨ False) → (p2 ∧ False)) → ((p5 ∨ p3) → ((p2 ∧ (p2 ∨ p3)) → p3))))) ∨ p2)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_185880683313849625776233355260 : ((((p1 → ((((p3 → True) ∧ False) ∧ False) ∧ False)) → p2) ∧ p5) → ((p2 ∨ ((((p1 → p3) ∧ (True ∨ True)) ∨ p5) ∨ p3)) ∨ (p2 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326387418712691921053281682330 : (p5 ∨ (p5 → (p4 ∨ ((((p3 → ((p4 → ((p4 ∨ (p1 ∨ False)) ∨ p3)) ∨ p1)) ∧ True) ∧ False) ∨ (((p5 ∨ p5) → (p3 ∧ p1)) ∨ p5))))) := by
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
theorem thm_5_vars_265865668012702316033738497369 : (True ∧ (p5 ∨ (p1 → ((((p2 → True) → ((False ∨ p4) ∧ p4)) → (p2 ∨ (((p2 → p5) → (False ∨ False)) ∨ (p4 ∧ (True ∧ p3))))) ∨ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62300983277177212091003663127 : ((p3 ∧ ((((((p3 ∨ ((False → p4) → (p1 ∨ ((p3 ∧ p2) ∧ p4)))) ∨ p5) ∨ p1) ∨ ((p2 ∨ p4) ∧ False)) → p3) ∧ (p5 → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801810815833234500103764435230 : (((p2 → ((p2 ∧ (p3 ∨ p1)) → (False ∨ (((p4 → (((p4 → True) → ((True ∧ (p5 ∧ p2)) ∨ p5)) ∨ p3)) ∨ p2) ∧ (p2 ∨ p5))))) ∨ p5) ∧ True) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113518805333074466645801325976 : ((((((p4 ∨ (False → True)) ∧ (p2 ∧ (p4 ∨ p4))) ∧ False) ∨ ((False ∧ p5) → ((p5 ∨ (p2 ∧ p4)) → p4))) ∨ (p2 ∧ p3)) ∨ (False ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111820784280104079806058128682 : (((((((((p5 ∧ False) ∧ True) ∨ ((p4 ∧ (p1 ∨ p2)) ∧ p3)) → (p4 → p5)) → p2) ∨ p4) ∧ ((False → p1) → p4)) ∨ p3) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150322869836436020087987730218 : ((p4 → (p1 → (((p2 → (p3 → False)) → ((p4 → ((True → True) ∧ (False ∧ p2))) ∨ False)) ∧ (False → p2)))) ∨ (p4 ∨ ((p3 → p3) ∨ p5))) := by
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
theorem thm_5_vars_788495780909487928756389503929 : (((p5 ∨ ((p2 ∧ ((p4 → p3) → (p3 → ((p5 ∨ (p1 ∧ (True → ((p2 → (False ∧ (p4 ∨ p3))) ∨ (p2 ∧ p3))))) → p4)))) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_217125217914683830852160625574 : ((((p4 ∨ p2) ∨ p1) ∨ False) → (((p2 ∨ p3) → (((False ∧ ((((p1 → True) ∧ (False ∧ False)) → (p1 ∨ p1)) → p3)) ∨ False) ∨ True)) ∨ p1)) := by
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
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135882208808376878755025108620 : (((p4 ∧ ((False ∧ ((False ∨ True) → (False → (p2 ∨ p2)))) ∨ p5)) ∨ (p5 ∨ (p4 ∨ (True → ((p3 ∧ False) → p4))))) ∨ (p5 → (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61474532284211111054517629346 : ((p1 ∧ (((((p2 → (p2 ∨ (p5 ∨ (((p1 ∧ False) ∨ p2) ∨ True)))) → (p3 → p1)) ∨ p3) ∨ ((p3 ∨ p1) ∧ p5)) → (p3 ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49099384113320116052588383768 : (((((((p4 ∨ (p4 ∨ False)) ∧ (False ∧ (((p3 → p1) ∨ p1) ∨ True))) → True) ∨ p5) → ((p3 ∨ p3) → p5)) ∨ (p5 ∨ (True ∨ p4))) ∨ p5) := by
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
theorem thm_5_vars_260282697508902344706828819813 : ((p2 → p4) → ((((((p1 → p1) ∨ ((p5 ∨ p2) → False)) ∧ p4) ∧ ((True ∧ p4) ∧ (True ∨ (False ∧ p4)))) → (p3 → (p5 ∧ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9873900648721481911458252760 : (((False ∧ ((True ∨ (p5 ∨ p2)) → (((p5 ∨ p1) ∨ p1) ∨ (p1 → ((p3 ∨ (((p2 ∨ p5) ∧ p3) ∧ (p2 ∨ p1))) → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57455775364659784884099766452 : (((p5 ∨ (p4 ∨ p3)) ∨ ((False ∧ p2) ∨ (False → (((((((p2 ∧ ((p4 ∨ p5) ∧ False)) ∨ False) ∧ p2) ∨ p3) ∧ p2) → p5) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9043034553649203555942333896 : (((((((p1 ∨ False) ∨ ((True ∨ (p5 ∧ p4)) ∧ (p4 ∨ p1))) ∧ p3) ∨ True) ∨ ((((p1 → p5) ∨ True) ∨ p5) → (p4 → False))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_78714335961209897294018313792 : (((((False ∨ (False ∨ (p3 ∧ (p2 → p2)))) → ((False ∧ p2) → (False ∨ False))) → (((p2 → True) ∧ (p4 → p3)) ∧ False)) ∧ (True → p1)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∨ (False ∨ (p3 ∧ (p2 → p2)))) → ((False ∧ p2) → (False ∨ False))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h4
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204993995893612922665949613362 : (((p5 ∧ (p2 ∨ (p5 → False))) → p4) ∨ (((p4 ∧ (p1 → True)) → p3) ∨ (((p5 ∧ (((p4 ∧ p1) ∨ False) ∧ (p4 → p1))) ∨ True) ∨ False))) := by
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
theorem thm_5_vars_114006069230514300693895308440 : (((((False ∨ (False → ((p5 → p5) ∧ ((p4 ∨ (p2 → p4)) ∧ False)))) → ((False ∧ p4) ∨ p3)) ∧ p4) ∨ (False ∨ (p4 → p4))) ∨ (True → p4)) := by
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
theorem thm_5_vars_304657530536322805264460569154 : (p1 ∨ ((p3 ∨ ((False ∨ (p2 → (p1 ∧ (False ∧ (p1 ∧ True))))) ∨ (False → ((p4 ∧ (False ∨ (True → p1))) ∨ (p3 ∨ p2))))) ∧ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192163361437898434292431999351 : (((((True ∨ False) → ((p5 ∨ p2) ∧ p5)) ∧ p5) ∧ p4) → ((p4 → False) ∨ (((p2 ∧ p4) ∧ (p4 ∨ ((p3 → False) → p2))) ∨ (p1 → p4)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156927211061982768177295759891 : ((((p1 → ((p3 ∧ (p3 ∧ (True ∧ (((False ∧ False) ∧ p2) ∨ p4)))) → (p4 → p3))) → p3) ∨ True) ∨ ((True → False) ∨ (p5 → (p2 ∧ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4231752527804029322271875747 : (p5 ∨ ((p3 → (p3 ∨ ((p3 ∨ True) ∧ (p5 ∧ p2)))) → (False ∨ ((((((p2 ∨ p4) → (p5 → p4)) ∧ p5) → p4) → p3) ∨ True)))) := by
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
theorem thm_5_vars_810098028564610998657411953889 : (((p5 → (((p4 ∧ (p2 ∧ ((p4 ∨ p2) ∧ ((False → (((p3 → True) → p5) ∨ p2)) ∧ p5)))) → p1) → (p3 → (p3 → (p2 ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116738994182610631388865554862 : (((p4 ∧ p1) ∨ (((((True ∨ p4) ∨ p2) ∧ ((((p3 → p4) ∨ (p5 ∧ p1)) ∧ p4) → ((p4 ∧ p2) ∧ p4))) ∨ p3) → p4)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43136331329286951478816570001 : (((((((((True ∧ (p2 ∨ True)) ∧ True) → True) → True) ∧ p4) → ((p2 ∧ ((p2 ∧ ((p1 ∧ p5) ∨ p2)) ∨ False)) ∨ p2)) ∧ True) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43031760509828380626687522927 : ((((((p1 → (p1 → (p1 ∨ (p2 → (((((False → True) ∨ (p1 → p3)) ∨ p3) ∧ p1) → p4))))) ∨ (False ∧ p4)) ∨ p3) ∧ p2) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337041701113239703302919152490 : (p1 → (((True ∧ (((False ∨ ((((False ∨ ((p4 → p1) ∧ True)) → p1) ∨ (True → (True → p1))) → p4)) ∧ p5) ∧ p4)) ∧ False) ∨ (False → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612512066430824738913062612116 : (((((((((((p5 ∨ ((p5 ∧ p5) → p2)) ∧ (False → p3)) ∧ p2) ∨ p1) → p1) ∨ (p1 ∨ (p2 ∧ p4))) ∨ p4) ∨ (p5 ∨ p1)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149033060592827067827660305718 : (((p1 ∧ (False ∨ p2)) ∨ ((((p4 ∧ True) ∨ True) → (p4 → (p1 ∧ ((p5 → (False → p1)) ∧ False)))) ∨ p2)) ∨ ((p2 ∧ p5) → (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47790859830151615352951628959 : ((((((p4 → (p5 ∨ ((p2 ∨ p4) → (True ∧ ((False → (p4 → False)) → p1))))) ∨ ((p3 ∨ True) → p2)) ∨ True) → False) → (p1 ∧ False)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 → (p5 ∨ ((p2 ∨ p4) → (True ∧ ((False → (p4 → False)) → p1))))) ∨ ((p3 ∨ True) → p2)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (((p4 → (p5 ∨ ((p2 ∨ p4) → (True ∧ ((False → (p4 → False)) → p1))))) ∨ ((p3 ∨ True) → p2)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42102419463976817080684008824 : ((((p1 ∧ p1) → ((True ∨ p1) ∧ (p5 ∨ (((p4 ∧ ((((False ∧ False) ∨ p3) → p2) → (False → p4))) ∧ False) ∧ (False ∧ p3))))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166451675476147018230925753306 : ((p2 ∨ ((p2 ∧ (p1 ∧ (p3 ∧ (p5 ∨ (p3 ∧ (True ∧ p2)))))) ∨ ((p3 ∧ True) → p3))) ∨ ((p5 ∧ p1) ∧ ((p2 ∨ (p4 ∧ p4)) → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651101546876802213689389099508 : ((((((p5 ∧ (p1 ∧ p5)) ∧ p3) ∨ (((p1 → (False ∨ (p1 ∧ True))) ∧ (p2 → (True → (p4 → p4)))) ∧ (p3 → p1))) ∧ (p4 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316522317165885331118388529164 : (p3 ∨ (p2 ∨ ((p4 → False) ∨ (((p2 ∨ (((p3 ∧ p3) ∧ p2) ∧ (True ∨ p4))) ∧ (((p3 ∨ p3) → False) ∧ (p4 → (p4 ∧ p2)))) ∨ True)))) := by
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
theorem thm_5_vars_136046597322922239536556272085 : (((p3 → (p3 ∧ (p5 → (p1 ∨ (False ∧ (p3 ∨ True)))))) → ((True ∧ (((p3 ∧ True) → True) → False)) ∧ (p1 ∨ p1))) ∨ (False → (True → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809332917479077816852954401188 : (((p5 → ((p4 ∧ ((((False ∨ p3) ∧ p5) → p2) → (((p4 → p2) ∨ p1) ∧ (((True ∧ p5) ∨ ((p3 ∨ p2) → False)) ∨ p2)))) ∨ True)) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324718640376816053703966134392 : (p5 ∨ (((p2 → False) ∨ p2) → ((p2 → p4) → (((p5 → (((p5 → True) → False) ∧ p3)) ∨ (True ∨ ((p5 ∨ p4) → p1))) → (p4 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    cases h1
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
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
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
      cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157937039281182254943869804219 : ((((False → (p2 → p5)) ∧ ((p3 ∧ p2) ∨ p4)) ∧ ((False ∨ (p1 ∧ p1)) ∨ ((p2 ∨ p1) → p2))) ∨ (False ∨ ((True ∨ False) ∨ (p5 ∧ False)))) := by
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
theorem thm_5_vars_386750833698456597510542356843 : ((((((p4 ∧ (p2 ∧ (True ∧ (p2 ∧ p5)))) → (((p4 → p2) ∧ p1) → (True ∧ ((p1 ∧ p1) ∨ (p1 → p1))))) → (True → p3)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_40106295595706100126060221168 : ((((((((((False ∧ (False → False)) ∨ (False → (p5 → (p5 ∧ p3)))) ∧ p5) ∨ p2) ∧ (p2 → p2)) ∧ p5) ∨ (p1 ∨ p3)) ∧ p3) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216284205235853522732868302553 : ((p2 → ((p2 → p4) ∧ p5)) ∨ ((((p3 ∧ p5) ∨ (p3 ∧ (p5 → ((p3 → False) ∧ True)))) ∨ (p4 ∧ (True → p3))) ∨ (False → (p4 ∧ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46708180567962615294823888581 : (((p4 ∨ ((p4 → p2) ∨ (((p3 ∧ ((p4 → ((p1 ∨ p3) ∧ (p4 ∨ p2))) ∨ p4)) → p2) ∧ ((p2 → False) ∧ p1)))) ∧ (p2 → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686946428697176087106448826954 : ((((p2 ∨ (((False → p4) → (False ∨ (((False ∨ (p2 ∨ (p2 → p2))) ∨ p1) → p2))) → p4)) → ((p2 ∨ p3) ∨ (p3 ∨ (False ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_495648505475266202448465500599 : ((((p4 → ((p3 → p3) → p3)) → ((p3 → (True ∧ ((False → (p5 ∧ (p5 → (p3 → p1)))) ∨ p2))) → (((p5 ∧ p2) ∧ p5) → p5))) ∧ True) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59796303299378482629789616249 : (((p2 ∧ p3) → ((p5 → (p5 → (p1 ∨ (p3 → ((p1 ∨ ((p1 → p2) → (p3 ∨ p1))) ∧ p3))))) ∧ ((p4 ∧ False) ∨ (p5 ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732281470520532681776845979168 : ((((False ∧ False) ∧ (((((((p3 ∨ p2) ∨ (p2 → False)) ∨ False) ∨ p3) ∧ False) ∧ (((p1 → (True ∨ False)) ∨ False) ∨ (p1 → p5))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53891952579870937817578192809 : (((False ∧ ((False ∨ p1) ∧ ((p2 ∨ True) → (True ∧ p1)))) ∨ (((p4 ∨ p4) ∨ (True → (False ∨ (p3 ∨ p5)))) ∧ ((p1 ∧ p5) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164809130561993166280767270741 : ((((p2 ∧ False) ∧ ((((p1 ∨ p5) → p3) → p4) ∨ ((p1 → (False ∨ p2)) ∨ p4))) ∨ True) ∨ (False ∨ ((p3 ∧ p3) → (p1 → (p1 ∧ p2))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168397279327433077282624442081 : (((p4 → p3) ∨ ((p5 → (False ∨ p3)) ∨ (((p2 ∨ p5) ∧ (p2 ∧ (p3 ∨ False))) → False))) → (((p4 ∨ (p3 ∧ p5)) → (p4 → p5)) ∨ True)) := by
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
theorem thm_5_vars_49156703654856864615653375838 : ((((((p4 ∨ p2) ∧ ((True → True) → p2)) → p5) → (p5 → (((p3 → p2) → p3) ∨ (True ∨ (p1 → p2))))) ∨ (p2 ∧ (p2 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324297792467572625802591469734 : (p5 ∨ ((((p4 → p2) → False) ∨ (p5 → (p5 ∨ p2))) → (True → ((p3 ∧ ((p3 → p1) ∨ ((p4 → p1) ∧ p4))) ∨ ((p4 ∨ p1) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67416482916930139178755549722 : ((p1 → ((((p1 ∧ p2) ∧ ((p5 ∧ p5) ∨ (True → p3))) ∨ (((True → (False ∧ (p5 ∧ (p3 → p3)))) ∨ False) ∨ p4)) ∨ (p5 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114491802491759112100393751738 : (((((p3 → ((False → (True → p3)) ∧ (False → p1))) ∨ p1) → (p3 ∧ (p1 → (p1 ∨ p4)))) → (((False ∨ p4) → p3) ∧ False)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727954508336844686088466591036 : ((((p3 ∨ (True ∧ p1)) ∨ (True ∧ (((p1 ∧ (p1 ∨ (p3 ∧ True))) ∨ p3) ∨ ((False → (p4 ∧ (((p3 ∧ p4) → False) → p5))) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166018864499381191162671273567 : (((p4 ∨ False) ∨ ((p1 → ((p3 ∨ (p3 ∧ p3)) ∧ p1)) ∨ (p2 → (p3 → (p3 → p2))))) ∨ ((p5 ∨ True) → (((p4 ∧ p3) ∨ p2) ∨ p1))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343034822918222981535934757999 : (p2 → (((False ∨ False) ∨ (p2 → False)) → (p5 ∨ ((p1 → (p2 ∧ (((p5 ∨ p4) ∨ False) → ((p3 → (False ∧ p1)) → (p2 → p3))))) ∧ p3)))) := by
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
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299329707815361083215381327193 : (False ∨ ((((p2 ∨ p1) ∨ (False ∨ False)) ∨ (((False ∨ (p1 ∨ ((True ∧ (p5 → p5)) ∨ ((False → p1) ∨ p3)))) ∨ (p2 ∧ True)) ∨ p2)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135199757686494799730998891556 : (((((p4 → (p4 ∧ p5)) ∧ (True ∨ (p3 ∨ (((p3 → p4) ∨ p5) → (p3 → p1))))) ∧ (True ∧ p4)) → (False ∨ p3)) ∨ (True → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50102597549474044050999056604 : (((p5 ∧ ((((p2 ∨ (p1 ∨ ((p5 ∨ True) → p5))) ∧ p1) → (((True ∨ False) ∨ p1) ∧ p2)) ∨ p3)) ∧ (p5 → ((p5 ∧ p4) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65834620249377861812349423046 : ((p4 ∨ (((p2 ∨ False) → (p3 ∨ p4)) → (((True ∨ (((p1 → p1) ∨ (p5 ∧ p2)) ∧ ((p5 ∨ False) → True))) ∧ (p3 → False)) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305158467831609418678166711771 : (p1 ∨ (((((p2 ∧ p4) ∨ (((False ∨ (p1 ∧ (False → p5))) ∧ True) ∨ (p4 ∨ (p4 → p4)))) ∧ True) ∨ True) ∨ (((True ∨ p3) ∨ p3) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687288085359462539915894963591 : (((((((p3 → ((False → p4) ∨ p1)) ∧ p3) ∧ ((True → (p3 → p4)) ∧ p5)) ∧ p1) ∧ ((p5 ∧ True) ∨ ((p3 ∨ (p4 → True)) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194032641064451539578385495806 : ((p5 ∨ (((p2 → True) ∨ (p1 ∨ (False ∨ p3))) ∧ True)) → (((p4 → (p3 ∨ True)) ∧ (False ∨ p5)) ∨ ((False ∨ True) ∨ (p1 ∧ (p3 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179791832530218754561799109389 : (((((p5 → p4) → p3) → ((p5 ∧ True) ∨ (False ∧ (p2 → False)))) ∧ p3) → ((False ∧ p3) ∨ (False ∨ (p3 → ((p2 → p2) ∧ (p5 ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
  -- One of the premise coincides with the conclusion.
  exact h5
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : ((p5 → p4) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h6
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609524722589777278330106184257 : (((((p2 ∧ (((True ∨ (False ∧ p3)) ∨ True) → ((((p1 ∧ (True ∧ ((p1 → p5) ∧ p4))) ∨ p2) ∧ (True ∨ True)) ∨ p4))) ∨ p4) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_610432021241551961886360502926 : ((((((((p2 ∧ p1) → (p3 ∨ (p5 ∨ p2))) → (p3 ∨ ((p2 ∧ ((p1 ∧ ((p5 ∧ p1) ∧ p1)) → p3)) ∨ p3))) → p1) → p5) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



