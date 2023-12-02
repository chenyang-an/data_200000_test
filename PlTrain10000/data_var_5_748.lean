variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677022047883618182699639284494 : ((((p2 → ((False ∧ ((p5 ∧ (((p1 ∧ p5) ∧ (p3 ∧ ((p2 ∨ False) ∨ False))) → True)) ∨ p4)) ∧ p3)) ∧ ((p3 ∧ (p3 ∨ p1)) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308436854045987452737340234027 : (p2 ∨ (((p3 ∧ (True → (p4 ∨ (p2 → (((p5 → (((p2 ∧ True) ∨ (True → (p1 ∨ False))) ∨ False)) ∧ (p1 ∧ p4)) ∧ p2))))) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116098919855849467025287841716 : ((((p4 → p4) ∨ p5) ∧ ((p3 → ((p2 ∧ (((p1 → p2) ∨ p5) ∧ (p1 ∧ ((True → False) ∧ p1)))) ∨ (False ∧ p1))) ∨ p2)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60046770917092922331399358859 : (((p1 ∨ p5) → (p2 → (False ∨ ((True ∧ (p5 ∨ ((((p3 → (p2 → p4)) ∨ ((p5 ∧ False) → p2)) → p4) ∨ p5))) ∨ (p1 ∧ p1))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207290055959958384570999518761 : ((((p4 ∧ (False ∧ False)) → p4) ∨ p2) → ((p1 ∨ ((((p3 → p5) ∧ (p5 ∨ ((((True ∨ p3) ∧ False) ∧ p1) ∧ p5))) ∨ p4) → p1)) ∨ True)) := by
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
theorem thm_5_vars_464821346406014025919473718848 : (((((p4 → (False ∧ p3)) ∨ ((((p1 ∨ (True ∧ p1)) ∧ p1) → p4) ∨ (p3 → p1))) → ((p2 ∨ False) ∨ (False ∨ (False → (p3 ∨ True))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312996596662112096472254972094 : (p3 ∨ ((((p5 ∨ (((p2 → (p1 ∨ (p4 → False))) → p3) → (p1 → (p2 ∧ (((p3 ∧ (p1 → p4)) ∨ p1) ∧ p3))))) ∨ True) ∨ p5) ∨ p1)) := by
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
theorem thm_5_vars_250020320156630468097142360815 : ((True → p3) ∨ (((((False → True) ∨ False) ∧ p4) ∧ ((p2 ∧ p3) → ((p5 ∨ (p1 ∨ (((True ∨ False) ∧ p2) → (p1 ∨ p5)))) → p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321227485523735994467335376039 : (p4 ∨ (p4 ∨ (((((p3 ∧ p1) ∨ (p4 → False)) ∨ ((p1 ∨ p5) ∨ True)) ∨ ((((True → p2) ∨ ((p2 ∧ p2) ∧ p3)) ∧ p2) → p5)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_226611114849998789446512683847 : (((p5 → p3) ∨ p4) ∨ ((((p3 → ((p4 → p4) ∨ p2)) → True) ∧ (p1 ∧ (((p1 ∨ ((p5 ∨ (p1 ∨ p2)) ∧ p5)) ∨ p3) ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234193466589481301962749140941 : ((False → (p1 ∧ False)) → ((((p1 → (((p1 → (p3 → (False ∨ p2))) → (False ∧ p2)) ∧ False)) ∨ (p3 ∨ ((p5 ∧ False) ∧ True))) → p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354868227405836194263592979249 : (p5 → ((True ∧ (((True ∨ p1) ∧ True) → (True ∧ ((False → (p2 → p1)) → ((((p3 ∨ p5) ∨ (p3 ∧ p3)) ∨ p4) → (p3 ∨ p4)))))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114004221967362666620507001863 : (((((p1 ∨ (p2 ∨ (False → (((p4 ∨ ((True ∧ p5) ∨ p2)) ∨ (p3 → False)) ∨ False)))) → p1) ∧ p5) ∨ (p4 ∨ (False → p3))) ∨ (p4 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171679209873736056779358668303 : (((p1 ∨ (p3 → (((True ∧ (p2 ∨ (p4 → (p2 ∨ p5)))) ∨ p2) ∨ p1))) ∨ p4) ∨ (((p1 → ((p1 ∨ (p3 ∨ p5)) ∨ p5)) ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683669698819217758305912892526 : ((((((p2 ∧ False) ∨ (((False ∨ (p4 → (p3 → p5))) ∨ p3) → ((p1 ∧ True) ∨ p5))) ∧ p4) ∨ ((False ∧ p1) → ((p5 ∧ p4) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190731839583337041125909547999 : ((((p2 → p5) ∨ (True ∧ (p4 ∨ p3))) ∧ (p4 ∧ p4)) ∨ (((True ∨ (((False ∧ (p4 ∨ (p5 ∧ (p3 ∨ p5)))) ∧ p5) ∨ p1)) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729422856108044785627296640284 : (((((p5 ∧ False) ∨ True) → ((((True ∧ False) → p5) ∧ (p2 ∨ (p5 ∧ False))) ∨ ((p2 ∧ ((p3 ∧ (False → (p3 ∧ p2))) ∧ False)) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194158697961644126745075400702 : ((p1 → (p2 → (True ∨ (False ∧ ((p5 ∧ False) → p4))))) → (False ∨ ((((p4 ∨ p2) ∧ p2) ∧ ((p5 ∨ p2) → ((False → True) ∧ p5))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43262980136615065207249590582 : ((((p3 → ((p5 → (True → ((((p5 → ((False → p3) ∧ p1)) ∨ (((p2 ∨ p5) → False) ∨ p4)) ∨ p1) ∧ p2))) → p1)) ∧ p5) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_919564367490011075962524152730 : ((((True ∧ (False ∨ ((p5 → ((p3 → p5) → ((True ∨ True) ∨ p2))) ∧ p2))) ∧ (p1 ∧ (p1 → (p2 ∧ (p2 → ((p5 ∧ p5) ∧ False)))))) → False) ∧ True) := by
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
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h16 := h14 h15
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- False on the left can always be used.
    apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810289672811766978364384180477 : (((p5 → (((((p5 → True) ∨ (p4 → False)) ∨ (p4 → (p5 ∧ p2))) → p2) ∨ (p3 ∨ (((p4 ∧ False) ∨ ((True → True) ∨ p2)) ∨ p1)))) ∨ p4) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171650427253108847660343983564 : (((True ∧ ((p4 ∧ (((True ∧ p1) → False) ∨ (p1 → p4))) ∨ (True ∧ False))) ∨ p1) ∨ ((False ∧ ((False ∧ True) ∧ ((p4 → p5) → p5))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655987193881287929417068421123 : ((((((((((p3 → p2) ∨ p2) → ((True → p3) ∧ p5)) ∧ p2) ∨ False) → (p5 ∧ p1)) ∨ ((False ∨ (p2 ∨ p3)) ∨ p1)) ∨ (p3 ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_40852206208137203593445999400 : ((((((((p5 → False) → False) → (p2 → p4)) → (True → ((p1 ∧ ((p5 → (p2 ∧ p3)) ∧ p4)) ∧ p3))) ∧ p5) ∧ (False ∨ p4)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55131253563062729018609939464 : ((((p1 ∨ ((p4 ∧ p5) ∨ p5)) ∧ p3) ∨ ((p2 → p5) ∧ (((p5 ∨ (p3 → (p1 ∨ (p1 → (p3 ∧ (p3 → p5)))))) ∧ p3) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58116877655208170963468910613 : (((p1 ∧ p5) ∧ (p1 ∧ (((p2 ∧ (((((p1 ∨ p5) → p3) ∨ False) ∧ (p3 ∧ (p1 ∧ p5))) → (p2 ∨ True))) ∧ p3) ∨ (p1 ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330948181784080235177141559507 : (True → (p4 → (p2 ∨ ((False → ((p1 → ((p5 ∨ p4) ∨ (p2 ∨ p5))) ∧ True)) → ((((False ∧ ((p5 → p1) ∨ p4)) → False) → p3) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263592185924199167238412957749 : (True ∧ ((p4 → ((p1 ∨ False) ∨ (((p5 ∧ p5) ∨ (p3 ∨ ((p4 → (p1 ∨ (p2 → p2))) → p4))) ∨ False))) ∨ (((False ∨ False) ∨ False) ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56050676755460480935884126357 : (((((p2 → p2) ∧ p1) → False) ∨ (True → (((p1 ∨ (p5 → p1)) ∧ ((p3 → (p3 ∧ ((p1 ∧ p5) → p2))) → (p2 ∧ p4))) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123915820416388891159353401162 : ((((True ∨ (p5 ∨ (((True → (p4 ∨ p3)) ∨ p3) → False))) → p5) ∧ (False → (((p1 ∨ (p4 ∨ True)) → (True ∨ p3)) ∧ p3))) → (p1 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (True ∨ (p5 ∨ (((True → (p4 ∨ p3)) ∨ p3) → False))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244328178332133889978061453950 : ((False ∧ False) ∨ (((((False ∧ p4) ∧ p1) ∨ True) ∧ ((((p1 → p2) ∧ p3) ∨ p1) ∨ (False → (p5 ∧ p1)))) ∨ (p4 → (p5 → (p4 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145123622815507581324732344468 : ((((True ∨ True) → (((False ∧ p5) ∧ False) ∨ (p1 ∧ p5))) ∨ ((p3 ∨ p4) → (p5 → (p4 ∨ (False → False))))) ∧ ((False ∧ (p2 ∧ p3)) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678228558205023458917776531298 : (((((True → (p4 ∨ ((p1 ∧ p1) ∨ (False ∨ (False ∨ p1))))) ∨ ((True ∨ p5) ∨ ((p2 ∧ p3) ∧ True))) ∨ (((True ∧ False) → p5) ∧ p3)) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46107418289616029065937514423 : ((((False ∧ ((p2 ∨ p5) ∨ (p3 ∨ (((p3 → True) ∧ (p4 → (((p5 ∨ (False ∨ p4)) → p4) ∨ p3))) ∧ p5)))) ∨ p4) ∧ (p5 → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806367917398472290261117663547 : (((p4 → ((False ∨ ((((p3 ∧ (p5 ∨ (p3 → p4))) ∧ True) ∧ p2) ∨ (p1 → (((p3 ∧ p5) ∨ ((p3 ∨ p4) ∨ p5)) ∧ True)))) ∨ p4)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_231438812911653836661563139306 : (((p2 → p1) ∨ False) → (p2 → (((True ∨ False) ∨ p3) ∧ ((p4 ∧ (True ∨ p4)) → (False ∨ (p5 ∨ ((p4 → False) → (p3 ∧ (p5 ∧ p4))))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h11 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h12 := h10 h11
      -- False on the left can always be used.
      apply False.elim h12
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h13 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h14 := h10 h13
      -- False on the left can always be used.
      apply False.elim h14
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h19 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h20 := h18 h19
      -- False on the left can always be used.
      apply False.elim h20
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h21 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h22 := h18 h21
      -- False on the left can always be used.
      apply False.elim h22
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h23 =>
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171580082692836426583343693381 : (((((True ∧ (True ∨ (p5 ∧ (p5 ∨ (False ∨ False))))) → p5) → (p4 → p3)) ∨ p5) ∨ (p3 → (((True ∨ p5) → ((p4 ∧ p1) → p1)) ∨ False))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168163400854982205882695594614 : ((((True ∨ p3) → False) ∧ (((True → p3) ∨ ((p1 ∨ False) ∨ p3)) ∧ (p2 → (p1 → p2)))) → (p4 ∨ (p3 ∨ (p1 → (p4 ∨ (p3 ∧ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : (True ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h12 : (True ∨ p3) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h13 := h2 h12
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_491754913445636186096571219 : ((((((p3 ∧ False) ∨ (((p5 ∨ p1) ∧ p3) → ((False → (False → (p5 → False))) → p5))) ∨ ((p2 ∧ p4) → p3)) ∨ p5) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117029227935780130596822467805 : (((p2 ∨ p3) → (((p1 → ((p2 → p1) ∧ p1)) → p4) ∨ ((((((p2 ∧ (p2 → p2)) → p2) ∧ p1) ∨ p3) ∨ p5) ∨ p2))) ∨ (p4 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47395330751490295248419995446 : (((True ∧ (((p5 ∧ (p5 → (p4 → (False ∨ (True ∨ ((p5 ∧ (True ∧ p3)) ∧ p5)))))) ∧ ((p4 ∨ p2) ∧ True)) ∧ True)) ∨ (p3 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104664960943147502354983297002 : (((p5 ∧ (((((False ∧ (p4 ∨ p2)) ∨ ((p3 → (False ∨ True)) ∨ p1)) ∧ p5) ∧ ((True → p1) ∨ p3)) ∨ p2)) ∨ (p5 → p5)) ∧ (True → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164526508274861946296907440691 : ((((p3 ∨ ((p5 → (True → p2)) ∧ (((p3 ∨ True) ∨ p3) → True))) → (p4 ∧ True)) ∧ p4) ∨ ((p3 → ((p4 → (p4 ∨ p1)) ∨ p1)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171687871909584067581293868111 : (((p4 ∨ (p2 ∨ ((True ∧ (True ∧ ((p5 ∨ True) ∨ p3))) → (p5 ∨ False)))) ∨ p2) ∨ ((p5 ∨ (p1 ∨ p1)) → (True → (p1 ∨ (p2 → True))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41156120206727576944234619144 : ((((p1 ∧ (p3 ∧ ((p3 ∨ ((True ∨ (p1 ∨ (p2 ∧ p1))) → True)) ∨ ((p4 ∧ False) ∨ (p2 → p4))))) ∨ ((p5 → p5) → p1)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197090954404219704349754143912 : (((p2 ∧ (p1 ∧ ((p3 → False) ∧ False))) ∨ p3) ∨ (True ∨ (p2 → (p4 ∧ (((p3 ∨ p1) → ((False ∨ p4) → (p5 → p1))) ∨ (p5 → False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317035164110776601406839718336 : (p3 ∨ (p4 → ((((False ∨ ((p3 ∨ (p3 → True)) → True)) ∧ (p2 ∧ p5)) ∨ (((p2 ∨ (p1 → ((p4 → p4) → True))) ∨ p2) ∨ p2)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756330132864329798161427448205 : (((p1 ∧ ((p3 → ((True → ((p4 → (p2 ∨ (p3 ∧ p2))) ∧ (True ∧ ((True ∨ p3) ∧ (p3 → (p5 → p4)))))) → p3)) → (False ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216888461778383088706886257309 : (((p2 ∨ (True → False)) ∧ p1) → (((True → ((p5 ∨ p3) ∨ p5)) ∨ p1) ∧ ((p1 → (p3 ∧ ((((p1 ∧ False) → p3) → p2) ∨ True))) ∨ p1))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111899243524495280512562866323 : (((((p5 ∨ (p2 → ((p3 ∨ (p2 ∨ p3)) → (p5 → (p3 ∨ p5))))) ∧ p5) → (((p3 → False) ∨ (p5 → p2)) ∨ False)) ∨ p2) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261274712187549001349585156517 : ((p5 → True) → (((((p5 ∨ (True ∧ False)) ∧ True) ∧ ((False ∧ p4) ∧ (p2 ∨ p1))) ∧ p5) ∨ (True ∨ ((p2 → ((True ∧ p3) ∨ p3)) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305287407984841634210585518789 : (p1 ∨ (((p5 ∧ ((((True → True) ∧ p5) ∨ (p4 ∧ ((p4 ∧ (p1 ∧ p3)) ∧ p3))) ∧ p3)) ∧ False) ∨ (((True ∨ p3) → p3) → (False ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178499864876476520821719152488 : (((False ∨ (((False ∨ (p1 ∨ p5)) ∧ p2) ∧ False)) ∨ (False → (p3 ∧ p1))) ∨ ((((p3 → p1) → p5) ∧ False) ∧ (True → ((p4 → p2) ∨ p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_218306618866566980689980995355 : (((p5 ∨ p1) ∨ (p1 ∨ p2)) → (((((False → p2) → ((False ∨ False) ∧ ((False ∧ p1) ∧ p3))) ∨ False) ∨ ((False ∧ (p1 ∨ p5)) ∨ True)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44440473233962526453439421092 : ((((p3 ∨ (False ∨ (((p5 ∨ (p4 ∨ (p2 → p4))) ∨ p2) ∨ p4))) ∧ ((p2 ∨ ((True ∨ p5) ∨ (p5 ∧ (p2 ∧ True)))) ∧ p1)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118156938351970464548156716345 : ((False ∨ ((p1 → (True ∧ (False ∧ p2))) ∨ (p5 ∧ ((((((False ∨ p5) ∨ p3) ∨ (True ∧ p3)) ∨ p2) → (p4 ∧ p5)) ∨ p1)))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773139823025668502529254657745 : (((False ∨ ((((((p3 → True) → p4) ∨ (p4 ∨ (((((p4 ∨ p3) ∨ p2) → p3) → p4) ∧ p3))) → ((True ∧ False) ∨ p5)) ∧ p2) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119289778920861904745476993704 : ((p3 → ((p5 ∨ ((((False ∨ (True ∨ ((p1 ∨ p3) ∨ p4))) ∧ p5) ∨ p2) ∨ ((p1 ∨ p5) → ((p1 ∧ p5) ∧ p3)))) ∨ p1)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49565634492433077254595338693 : ((((((p3 ∧ p4) → p1) ∨ (p4 → (((True ∧ p5) ∨ p1) ∨ ((True ∧ p4) ∧ p5)))) → ((p3 ∧ p2) → p1)) → ((p3 ∨ p4) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64127263863850213212264602139 : ((False ∨ ((((False ∨ p5) ∧ p1) ∧ True) ∨ ((((False ∧ (p5 ∧ False)) ∧ (p4 → (p5 → p1))) → p2) ∧ ((p3 → (p3 ∨ p5)) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311959368480460698310649105953 : (p2 ∨ (p3 ∨ ((p2 ∨ p4) ∨ (((p5 → (p5 ∨ ((False → True) ∧ ((False ∨ p1) ∧ ((p4 ∨ p2) → ((p1 → p2) ∧ p2)))))) → False) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → (p5 ∨ ((False → True) ∧ ((False ∨ p1) ∧ ((p4 ∨ p2) → ((p1 → p2) ∧ p2)))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158963293060995532297556453246 : ((p2 ∨ (p2 → (True → ((p5 ∨ (p1 ∨ (False ∨ p2))) ∧ (p1 ∧ ((p3 → (p5 ∨ p1)) ∧ p3)))))) ∨ (((False → False) ∨ (p5 ∧ False)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659897797005760702177593879802 : (((((((p4 → ((True ∨ (False → (p1 ∨ p2))) ∨ (p2 ∨ ((False ∨ (p1 → (False ∨ p5))) → p3)))) ∨ p4) ∧ p2) ∨ False) → (p5 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45334169869253809440957029814 : (((p3 ∧ (p2 ∧ ((True → ((False → (p4 ∨ ((p4 ∨ p1) → (p4 ∧ (p2 ∧ p2))))) ∧ False)) ∧ ((True → p3) ∧ (p5 → p3))))) → p5) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h11 := h6 h10
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149374481466520225068766025268 : (((p2 → False) → (((((p1 ∨ False) → False) → (((p3 → p1) → (p3 ∨ p2)) ∧ p4)) → p3) ∨ (True ∧ True))) ∨ ((False → (p5 → p3)) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349863906373350825342226242882 : (p4 → ((False ∨ (((p4 → (p5 → p4)) → ((((p4 ∧ p1) ∨ (p1 → p3)) → (False ∨ p2)) ∨ p2)) ∨ (p4 → (p2 → (True → p2))))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66136879289915118785111102771 : ((p5 ∨ (((((p1 ∨ p2) ∨ ((p4 → ((p2 → (p1 → p5)) ∨ ((p5 ∨ p2) → p3))) ∧ p4)) ∨ (p4 → True)) ∨ p5) ∨ (p2 ∨ p1))) ∨ False) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117188968966680105665339273532 : ((True ∧ ((False ∨ (((False ∨ (((p1 ∨ ((p2 → p5) ∧ p3)) ∧ (p4 → p2)) → p5)) ∨ p2) → p1)) ∨ ((p2 ∧ p2) ∨ True))) ∨ (p2 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_231591246507208524057589083292 : (((True ∧ False) → p1) → ((False → p2) → (p4 → (((True ∧ (((((p3 ∧ False) ∧ p5) ∨ (p5 → True)) ∨ (p3 ∨ p5)) ∨ p1)) → p2) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68618029255121195709188453805 : ((p4 → ((((p2 ∧ p4) ∧ (p2 ∧ (p5 ∧ p1))) ∨ ((((((p2 ∨ (True → p4)) ∧ p5) ∨ p5) ∧ p2) ∨ (p4 ∨ p5)) ∧ p5)) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48005035235055473087745888215 : (((((((True → p3) → (False ∨ (False ∧ (p5 → p4)))) → p5) ∨ (True ∧ True)) → (((p3 ∧ p2) ∨ p2) → (False ∨ p4))) → (p2 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48058143671015022007075774119 : (((((p1 ∨ (p1 ∨ (True ∧ (True ∨ p5)))) → p2) ∨ (p1 → ((True ∧ ((False ∧ (p3 ∨ (True → p1))) ∧ p3)) ∧ True))) → (p3 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120958187705661480607307307097 : (((((False → p5) ∨ p4) ∨ (((((p4 → p3) → p2) ∨ p5) ∧ (True ∨ (True ∨ (((False ∨ False) ∧ False) ∧ p5)))) ∨ p3)) ∨ False) → (p1 ∨ True)) := by
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h11 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h12 =>
            -- Disjunctions on the left can always be decomposed.
            cases h12
            case inl h13 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h14 =>
              -- Conjunctions on the left can always be decomposed.
              let h15 := h14.left
              let h16 := h14.right
              -- Conjunctions on the left can always be decomposed.
              let h17 := h15.left
              let h18 := h15.right
              -- Disjunctions on the left can always be decomposed.
              cases h17
              case inl h19 =>
                -- False on the left can always be used.
                apply False.elim h19
              case inr h20 =>
                -- False on the left can always be used.
                apply False.elim h20
        case inr h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h22 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h23 =>
            -- Disjunctions on the left can always be decomposed.
            cases h23
            case inl h24 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h25 =>
              -- Conjunctions on the left can always be decomposed.
              let h26 := h25.left
              let h27 := h25.right
              -- Conjunctions on the left can always be decomposed.
              let h28 := h26.left
              let h29 := h26.right
              -- Disjunctions on the left can always be decomposed.
              cases h28
              case inl h30 =>
                -- False on the left can always be used.
                apply False.elim h30
              case inr h31 =>
                -- False on the left can always be used.
                apply False.elim h31
      case inr h32 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h33 =>
    -- False on the left can always be used.
    apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_982999501946835751895077859900 : (((p1 ∧ (((((False ∧ ((((p3 ∨ p3) ∧ p1) ∨ p5) ∧ (p4 ∧ p5))) ∨ (False → False)) ∨ p1) → False) ∧ (((p1 ∨ p1) ∧ p5) ∨ p1))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h10 : (((False ∧ ((((p3 ∨ p3) ∧ p1) ∨ p5) ∧ (p4 ∧ p5))) ∨ (False → False)) ∨ p1) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h11 := h4 h10
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h13 : (((False ∧ ((((p3 ∨ p3) ∧ p1) ∨ p5) ∧ (p4 ∧ p5))) ∨ (False → False)) ∨ p1) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h14 := h4 h13
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h16 : (((False ∧ ((((p3 ∨ p3) ∧ p1) ∨ p5) ∧ (p4 ∧ p5))) ∨ (False → False)) ∨ p1) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h17 := h4 h16
    -- False on the left can always be used.
    apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53756998859290396429280658039 : (((((p2 ∧ p1) ∨ ((p3 ∨ (False ∧ p5)) ∧ p3)) ∧ True) ∨ (((p5 ∧ p5) ∧ (p1 ∧ ((p5 ∧ ((False ∨ False) → True)) → False))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111577632722384449883946608293 : (((((p4 → p1) → (p3 ∧ ((p1 ∧ (((((p3 ∧ (p5 ∨ p3)) ∨ p4) ∧ p2) ∨ p2) → p1)) ∧ (p1 → p5)))) ∧ p2) ∨ True) ∨ (p4 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300971812765615516933251291553 : (False ∨ (((p4 ∨ p2) ∨ (((p5 ∨ p1) ∨ (True ∨ (False → p2))) ∨ p1)) ∨ ((p4 ∨ (p5 → ((p2 ∧ (p1 → (p3 ∨ p4))) ∧ p1))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750720895737605079498167194392 : (((True ∧ ((p3 ∧ (p3 → ((True ∨ p3) ∨ ((p4 ∨ p2) ∨ ((p3 ∨ True) → True))))) ∨ (((True ∧ (False ∨ (p4 ∨ p5))) → p3) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149967998254218759607104161219 : ((p4 ∨ ((p5 → ((((p3 ∨ False) ∧ (True → p1)) ∨ (((p3 → True) ∨ False) ∧ p5)) → False)) ∨ (False → False))) ∨ ((p3 → p1) → (p4 ∧ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80804674303414992859633435142 : (((p5 → (((False ∧ (((((p1 → True) ∨ False) ∨ (p5 ∧ (True ∧ (False ∨ p3)))) → False) ∧ p5)) ∨ (p5 ∧ True)) ∨ p1)) → (p3 ∧ p5)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → (((False ∧ (((((p1 → True) ∨ False) ∨ (p5 ∧ (True ∧ (False ∨ p3)))) → False) ∧ p5)) ∨ (p5 ∧ True)) ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337259087748640722581733854903 : (p1 → ((True → ((p4 → ((p3 → (((p3 → (False → p3)) → p3) ∧ ((p4 → p5) ∧ (p5 ∧ (False ∧ False))))) ∨ p3)) ∧ False)) → (p1 ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198898052395077441749010732504 : ((p3 → (((p2 ∨ (p4 ∨ False)) → p2) → False)) ∨ (((((p5 ∧ (p2 ∨ p3)) ∧ p2) ∨ False) ∨ (False ∧ False)) ∨ (p5 → ((p4 ∧ True) → p5)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_237884926160208744349822113964 : ((True ∨ True) ∧ (((p5 ∨ ((p3 ∧ False) ∧ True)) ∧ (p1 ∧ ((p5 → p1) → ((p1 → p4) ∧ (((p5 ∨ False) ∨ p5) ∨ p2))))) ∨ (True ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149116938804215676079075859604 : (((False ∧ p1) ∧ ((True ∧ (((p4 ∨ p2) ∧ (False ∧ p2)) → ((p2 → p2) → ((p3 → False) ∧ p5)))) ∨ p2)) ∨ (((p2 → p5) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114462786915048472867884207463 : ((((((((False ∨ False) ∨ False) ∧ p3) ∧ True) ∨ (p5 ∨ ((p2 ∨ p5) → (p3 → p3)))) ∨ p3) → (p1 ∨ (False ∨ (p3 ∧ p3)))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721473439660414950859207344382 : ((((p2 ∧ ((p5 → p1) ∨ p2)) → ((False ∨ (((p2 ∧ p1) ∧ ((p4 → (p4 ∧ (p2 ∧ p3))) ∨ (p2 ∧ True))) ∨ (True → p3))) ∨ p2)) ∨ p5) ∧ True) := by
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
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42177441817672411559573313336 : (((True ∧ ((p5 ∧ ((p1 ∧ (p2 ∧ ((p5 → (p1 ∨ True)) ∧ ((False → (p5 → False)) ∨ ((False → p2) ∨ p2))))) ∧ False)) ∨ p5)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757693753328030487814911431408 : (((p1 ∧ (p5 ∧ (p1 ∨ (p2 ∨ ((((p2 → (p5 ∨ ((p2 ∧ False) ∨ (p5 ∨ False)))) ∧ ((True → (False → p2)) ∧ True)) → True) → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157168866849803761352493919217 : (((((((((False ∨ p4) ∧ p1) → p4) ∧ False) ∨ (p3 → ((p3 → False) ∧ p2))) ∨ p2) → True) → False) ∨ ((True ∧ ((p1 ∨ False) ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114274996604503857220921999006 : ((((((False → (p5 ∨ p1)) → (p3 ∧ ((p2 ∧ p1) ∧ p5))) ∧ (p3 ∨ (False ∨ True))) ∨ p1) ∧ (p4 ∧ ((p3 → p5) → p5))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165494243060477393720075203600 : ((((p1 ∨ p3) → ((False ∧ (True → p1)) ∨ (p2 ∧ p3))) ∨ ((p4 ∨ (p1 → True)) → p2)) ∨ (True ∨ (p1 ∧ ((p4 ∨ (True ∨ p1)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346582914631611316910604248494 : (p3 → ((((((p2 → ((((True ∨ p1) ∧ (p5 → p3)) ∨ (p4 ∨ True)) ∨ False)) ∨ (p3 ∨ p5)) → p5) ∨ p3) ∧ p2) ∨ ((p1 ∨ p1) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594505688822383994052190542196 : (((((((p3 → ((p1 ∨ ((p1 ∨ p1) ∨ p2)) ∨ p5)) ∧ p1) ∧ (p1 ∨ (p5 → p4))) ∨ ((p1 ∨ ((False ∧ True) ∨ False)) ∧ p5)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608652015362347397265522004006 : (((((((p3 ∨ ((True ∧ (((p5 ∨ p3) ∧ (p2 → p5)) ∨ (False → p4))) ∧ (False ∧ True))) ∨ (p5 ∧ False)) ∨ (p2 → p3)) ∨ False) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599281269168820733786745730479 : (((((False ∧ False) ∨ (p5 ∧ (((p3 ∨ p1) ∧ ((False ∨ (p5 ∨ p5)) → ((p3 ∨ False) ∨ (((p2 ∨ p3) ∨ True) ∧ p4)))) ∨ p2))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53271677880960753980901185629 : (((False ∧ (True → ((p3 → p2) ∨ ((True ∧ (p5 ∧ True)) ∨ p1)))) ∨ ((p2 → False) ∨ (((p4 ∧ (False ∨ True)) ∧ False) → (False ∨ p1)))) ∨ p4) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194826384193027293401021538354 : (((((p3 ∧ p3) ∧ (True ∨ p3)) ∧ p1) → True) ∧ (((p1 ∧ p4) ∨ ((p5 ∧ True) ∨ ((p1 → True) → p3))) → ((p5 ∧ p3) ∨ (p2 → p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158990614221472866203887410156 : ((p3 ∨ ((p3 ∧ p3) → (((((p3 ∧ (True → (True → True))) ∨ (True ∨ p4)) → p5) ∧ p2) → False))) ∨ (p4 ∨ (((p1 ∧ False) ∧ p4) → p2))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_958240690058837457814562129221 : ((((p2 → (False → True)) → ((((p4 ∨ p3) → p1) ∧ (((p1 ∧ p3) → True) ∨ (((True ∨ (p2 ∨ p4)) ∨ p5) ∨ (p4 ∨ True)))) ∧ False)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → (False → True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60454173204115461747240768518 : (((p5 → p1) → ((((p4 ∧ p4) ∧ (((p2 ∨ p5) ∨ (p3 ∨ p1)) ∧ p4)) → (p2 ∨ (p1 ∨ p3))) ∧ ((p3 ∧ (False ∨ p1)) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



