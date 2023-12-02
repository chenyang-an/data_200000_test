variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67600578240849408444120388691 : ((p1 → (p1 ∧ (((((p2 ∧ ((p4 → p5) ∧ (p5 ∧ (p2 ∨ (p3 ∨ p4))))) → p3) → (p2 ∨ (p1 → (False ∧ p2)))) ∨ p1) ∨ p3))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311883237967010488636046330335 : (p2 ∨ (p2 ∨ ((True → (True → (True ∧ ((False ∨ ((True ∨ (p1 ∧ p4)) → True)) ∧ ((p5 ∧ p4) ∧ True))))) → (False ∨ (p5 ∨ (p1 → p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301167700418606247333175870613 : (False ∨ (((((p3 ∨ p2) → p1) ∧ (p4 → p2)) ∧ p5) → ((p4 → p4) → (p2 ∨ (((p5 ∨ ((False ∧ True) ∨ (p1 ∧ True))) ∧ p1) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67992754563053895290020962258 : ((p2 → ((False ∧ p4) ∨ (True ∧ ((True ∧ ((((p1 ∨ p4) ∨ p3) ∧ ((p2 ∨ p2) ∨ ((False ∧ p1) → p3))) ∨ (p3 ∨ p5))) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46524074758657865324533378584 : ((((p5 → p1) ∧ ((p3 ∨ (p1 ∧ (True ∨ True))) → (((p1 ∨ (p4 ∧ ((False ∨ (True ∧ p1)) ∨ False))) ∧ p2) ∧ p3))) ∧ (p5 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134646802826271022626398314996 : (((((p3 ∨ ((((True → p3) → p4) ∧ p4) → (True ∧ False))) ∨ p5) ∨ ((p4 → (p4 ∨ (p3 ∧ p2))) ∨ True)) → p5) ∨ (True ∧ (False → p5))) := by
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
theorem thm_5_vars_137469680180179508851697018296 : ((p4 ∧ (p4 ∨ ((((p3 ∧ p1) ∨ p3) → (p1 → (p4 ∧ (p2 ∨ ((p2 ∧ p1) → ((p5 → p1) ∧ p5)))))) ∧ False))) ∨ ((p4 ∧ p1) → p4)) := by
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
theorem thm_5_vars_166425479492430686375740898727 : ((p1 ∨ (((False ∨ False) → False) → (((p2 ∨ (p1 → ((p2 ∧ p2) ∨ False))) ∨ p1) ∧ p2))) ∨ (p1 → (((p2 ∧ False) ∧ p1) → (p4 → False)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318570172778619387939617627582 : (p4 ∨ (((((p2 → p4) ∧ p2) ∧ ((p4 ∨ p3) ∨ (False → (((True ∧ True) ∧ p1) ∧ (True ∨ (True ∨ (p3 ∨ True))))))) → p5) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230421600174537698660428296254 : (((p4 ∨ p2) ∧ p1) → ((p5 → p1) ∧ ((p1 ∧ (True → ((((False ∨ (False ∧ p4)) → (False ∨ (p5 → p2))) ∨ (p2 ∧ p2)) → p4))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735459112346315075635066062703 : ((((p4 ∨ p3) ∧ (p2 ∧ (p5 → ((True ∨ (((p3 ∧ (((True ∨ p1) ∨ True) ∨ False)) ∨ (p2 → (p4 → (True ∨ p2)))) ∧ True)) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138433459720326206059925906356 : ((p5 → ((((((p1 ∨ p1) → p5) ∧ ((True ∧ False) ∨ p4)) ∧ p4) ∧ p5) ∨ ((p3 ∧ (p3 ∨ (p2 ∨ False))) ∨ p2))) ∨ ((True → False) → p2)) := by
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
theorem thm_5_vars_754086433225002837976332698228 : (((False ∧ (((False ∧ True) ∧ p4) ∧ ((True → (((p1 ∧ (p4 → p3)) ∨ (p3 ∧ p1)) → (p2 ∧ (p3 ∧ (p4 ∧ p4))))) ∨ (p3 → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260232734950748768315800724884 : ((p2 → p3) → ((((p4 ∨ (((False ∧ p4) ∨ (p4 ∧ (p2 → ((p1 ∨ (p2 → (True ∨ p2))) → p2)))) ∧ p4)) ∨ p5) ∨ True) ∨ (p3 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113270918753121154803308060215 : ((((((((p1 ∧ True) ∧ p3) ∨ (p1 → (p1 ∨ True))) ∨ (p5 ∨ True)) ∨ p2) ∧ ((p3 ∧ (False → p1)) ∨ p5)) ∧ (True ∧ False)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776131222376905380101085779208 : (((p1 ∨ ((((((p4 → ((p1 ∨ p2) ∨ ((True ∧ p5) → (True → ((p1 ∨ p1) ∨ False))))) ∨ (p4 ∨ p2)) ∨ p3) ∧ p1) ∨ p1) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608481005845259096378855188246 : (((((((((p2 ∨ p5) ∨ True) ∧ (((p2 ∧ False) ∧ (p2 ∨ (True ∧ p1))) → p2)) ∨ (((p3 ∨ p2) ∧ p2) ∧ p1)) → False) ∨ p1) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_134146941138460020069675331767 : ((((True ∨ (p3 ∨ ((p4 ∨ p4) → ((p5 ∧ ((p1 ∧ p1) ∨ p3)) → (p3 ∧ False))))) ∧ (False ∨ (p3 ∧ p5))) ∨ p4) ∨ (p2 ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117929340072767724775924270482 : ((p5 ∧ ((p4 ∨ p1) ∧ ((p5 ∧ (p3 → True)) ∧ (((((p5 → p1) ∧ ((p5 → (p3 ∧ p5)) → True)) ∨ p5) ∨ True) → p5)))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114282502016434243692058920333 : ((((((p3 → ((p4 ∧ p4) ∧ ((((p3 → True) → p2) ∨ p2) ∨ True))) → p1) → p1) → False) ∧ (p3 ∨ (p3 → (p5 ∧ p5)))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135462434649805213983273335817 : (((((p3 ∨ (p4 → (p2 → (((p1 ∧ p1) ∧ (p3 ∨ p4)) ∧ p3)))) ∧ p3) ∧ (p2 ∨ False)) → ((p3 → False) → p4)) ∨ (p1 ∨ (p1 ∨ p1))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h8 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h9 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h13 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h14 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h15 := h2 h14
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172499285891199402341364263294 : ((((True ∧ p2) ∧ p2) ∧ ((p4 ∨ (p2 ∨ (p4 → p3))) ∨ (p3 ∨ (False ∧ p4)))) ∨ ((p2 → ((p1 ∨ False) → p4)) → ((p1 → True) ∧ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166072237109801114863033159080 : (((True ∨ p5) → (p5 ∨ ((((((p5 ∧ p4) ∧ (p3 ∨ False)) → False) → p5) ∧ p3) ∨ True))) ∨ (p3 ∧ (((p5 → (p5 ∨ p5)) ∨ p1) ∧ p1))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147719459580027090134632303652 : ((((False ∨ ((p2 ∧ (p2 ∨ p5)) → (False → p5))) ∨ ((((p4 → p3) ∧ p5) → (p1 → p1)) → False)) → p4) ∨ ((p5 ∨ (False ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66608131611802982675803458183 : ((True → ((((True → ((p5 ∧ p1) ∨ p3)) → False) → (p3 → (False ∨ ((p4 → (p3 ∧ p3)) → False)))) ∨ ((True ∧ p4) ∨ (p5 → False)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True → ((p5 ∧ p1) ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76689125535928366429710343828 : ((((True → (((p2 ∨ ((False ∨ p4) ∨ ((p3 → (p5 → p1)) ∨ p3))) ∨ False) ∨ p5)) ∨ (p1 ∨ ((p3 → (p3 → p3)) ∨ p4))) → False) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True → (((p2 ∨ ((False ∨ p4) ∨ ((p3 → (p5 → p1)) ∨ p3))) ∨ False) ∨ p5)) ∨ (p1 ∨ ((p3 → (p3 → p3)) ∨ p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260373839102907376143774574078 : ((p2 → p5) → (((p1 ∧ p1) ∧ p1) → ((p2 ∧ (p1 → (p3 ∨ (((p1 → p1) ∧ p2) ∧ ((((p4 ∧ p1) → p2) ∧ p1) ∧ False))))) ∨ p1))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185776603447950583968192790209 : ((p4 → (False ∧ (((p1 → (True → p5)) → (False ∨ p2)) ∨ p1))) ∨ (False → ((False → p5) → (True → (p1 → ((p2 → p4) ∨ (p5 → p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69025503236865334560033732554 : ((p5 → ((((p1 → (((((((False → True) ∧ p2) ∨ True) → False) ∨ ((True → p5) ∧ (p3 → p4))) ∧ p2) ∨ True)) ∧ p4) ∨ p3) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56316928418988534488981586678 : ((((p2 ∨ (p4 ∧ p3)) ∧ p4) → ((((((p4 ∧ ((p5 ∨ (p2 ∨ (False ∧ p2))) → (p2 ∨ p3))) ∧ True) ∨ p1) → False) ∨ p4) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159317737336388980840747373946 : ((p5 → ((((False ∧ (((p2 ∨ p1) ∨ p3) ∧ False)) ∨ p5) ∨ p4) ∨ ((p2 ∧ (True → p5)) → p5))) ∨ ((((p4 ∨ False) ∧ p2) ∨ False) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300144355127155746297189086017 : (False ∨ ((p5 ∧ (((True ∨ (p5 ∨ p4)) → ((True → True) ∧ ((p3 ∧ (p4 ∨ ((p1 → False) → p4))) ∧ p5))) ∧ (p1 → p3))) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263923502936378163540393931170 : (True ∧ ((((p3 ∧ (p4 ∧ p4)) ∨ (p3 ∧ True)) ∨ ((p5 ∧ (p2 ∧ p4)) → p4)) → ((True → p1) ∨ ((p5 ∧ p2) → (False ∨ (False ∨ p5)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262205335525714714883313439358 : (True ∧ (((p1 ∧ (False → (((((p1 ∧ (p3 ∧ p2)) ∨ p1) ∨ (False ∧ (p5 → (p4 ∨ p2)))) ∨ True) ∨ (p3 → (False ∨ p3))))) → False) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55068172511711674027232187864 : (((p4 ∨ ((p1 → (p5 ∧ p2)) ∨ True)) ∧ (p2 ∧ ((p2 ∧ p2) → ((((p3 ∨ p3) ∧ ((p1 → (p5 ∨ p4)) ∨ p5)) ∨ p1) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40293801669455651407084415897 : ((((p5 → ((p3 ∧ (((p1 ∨ p3) ∧ (p1 ∧ (((p1 ∧ p4) ∧ p4) ∨ ((False ∨ (p1 ∨ False)) → p5)))) ∧ p2)) ∧ p5)) ∧ p4) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171407181441340518843318852254 : ((((True → (False → (p3 ∨ False))) → ((True ∧ p3) ∧ (p2 ∧ (p5 ∧ p5)))) ∧ True) ∨ (True ∨ ((p3 ∨ p2) → (False ∧ ((False ∨ p4) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692287080440438856250957943451 : ((((((((p4 ∧ p4) ∨ ((p1 ∨ (True → False)) ∨ False)) → p1) ∧ p5) → p2) ∧ (((p5 → p5) ∧ (False → p5)) ∨ (p5 ∨ (p2 → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204378927385449763056586335321 : (((p5 ∨ ((p2 ∧ False) ∧ False)) ∧ p5) ∨ (True → (((p4 ∧ ((True ∨ p3) ∧ True)) ∧ (p4 → ((True ∨ p4) ∧ p2))) ∨ (p2 → (p3 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54587067415670713978169296286 : (((p4 ∨ ((p4 → ((p5 → p1) ∨ p4)) → p1)) ∨ (((True ∨ (p4 ∨ ((((p4 ∧ (p1 ∧ p1)) ∧ p1) → p1) ∧ p4))) → p5) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648033713507378477337961761348 : ((((((((p4 ∧ (p2 ∧ p3)) ∨ True) → (False ∨ (p4 ∧ p4))) ∧ (((False → p1) ∧ ((p2 ∨ p3) → p1)) ∧ p5)) ∧ True) ∧ (p2 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314406074884581685471420976725 : (p3 ∨ (((((True ∧ p1) → (((p1 ∧ ((p2 ∧ p4) ∨ p5)) → p3) ∧ p5)) ∨ ((p5 → False) ∨ p5)) ∨ True) ∨ ((False → (False → p4)) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172933798083798696561051340157 : ((p3 ∧ (((((False → False) ∧ (p4 → False)) → p1) ∧ (p4 ∧ True)) ∧ (p4 → False))) ∨ ((p5 ∨ ((p2 ∧ p2) → (True ∧ (True ∨ p5)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191118827681514025764771864340 : (((p3 ∨ (p5 ∨ p1)) ∧ (p5 ∧ (p1 → (p5 ∨ p2)))) ∨ (((((p3 ∧ (p2 ∧ False)) → p3) ∨ (False ∨ True)) → ((p2 → True) ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172154899509256463054969298695 : (((((((p3 ∨ p1) ∧ p5) ∧ (p4 ∧ p5)) ∨ True) ∨ p1) ∨ (p3 → (p2 ∨ p5))) ∨ ((((p4 ∧ p4) ∧ p5) ∧ (p3 ∧ p3)) → (p2 → p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111803260168285559423205016810 : (((((p3 ∧ ((p5 → False) ∧ ((p4 ∨ (p5 ∧ (p1 ∧ ((p4 ∧ p2) → p5)))) → (False ∨ True)))) → p3) → (True → p2)) ∨ True) ∨ (p5 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207779960689308166307104292327 : (((p4 ∨ (p5 → (p1 ∨ p1))) → p1) → ((((p2 ∧ p3) ∧ (p3 ∨ (p5 → p2))) ∨ True) ∨ ((p5 ∧ p1) → (((p1 ∧ p1) ∧ p3) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119078254882827672402216395905 : ((p1 → ((p3 ∧ (p3 ∨ ((True → True) → ((p3 ∨ (p2 ∧ ((p5 ∨ (p5 → True)) ∧ p4))) ∧ p3)))) ∨ (p2 ∨ (p4 ∨ p1)))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301058042178233554072479690083 : (False ∨ ((((p3 → p1) ∧ p2) → ((p3 ∨ (p4 ∧ p1)) ∨ p3)) ∨ (((p5 ∧ (p1 ∨ p5)) ∨ p1) → (((p4 ∨ (True ∨ p2)) ∨ p5) ∧ True)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
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
theorem thm_5_vars_259027452235627095379266144859 : ((True → p4) → ((((((True → p1) ∧ p3) → p4) → False) ∨ (p1 ∨ (True ∨ (p4 → p5)))) ∧ (((p4 ∨ p4) ∧ p5) → ((False → p5) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624568811439129223278900067507 : ((((p4 ∨ (((((True ∧ ((((True → p1) → (p3 → (True → p3))) ∨ p5) ∧ p4)) ∧ p3) ∧ p1) ∧ p4) ∨ (p3 ∧ (p1 ∧ p2)))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_111085770294246804250752612381 : ((((p2 → (p4 ∧ (((False ∨ False) ∨ p4) ∧ (p2 → (p2 → True))))) ∧ ((((p1 → p3) ∨ (p1 → True)) ∨ p3) → p1)) ∧ p4) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110643062759909691640005267422 : ((p5 → ((True → (p3 ∨ (p2 ∧ (p5 → False)))) ∨ (p1 ∨ ((True ∧ (p3 → True)) → ((p4 ∧ (True → True)) ∨ (p4 → True)))))) ∧ (True ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171905999276034406077539284101 : (((False → ((p1 ∨ (p3 ∧ p3)) ∧ ((p3 → p2) ∧ (p4 ∧ (p4 → p4))))) → False) ∨ ((p1 ∧ ((p2 ∧ (p1 → p5)) ∨ False)) → (p5 ∨ p3))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_812503829685403254721199087 : ((p2 ∧ ((((False ∨ p2) ∨ p5) ∨ ((p4 → (p5 ∧ ((True ∧ (p5 ∧ ((p4 ∨ False) ∨ p3))) → p3))) ∨ p5)) → (True → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42293662127238553584987436132 : (((p2 ∧ (((((p5 → ((p1 ∨ ((p3 ∧ p3) ∨ ((False ∨ True) ∨ True))) ∨ p2)) → p4) ∨ (True ∧ p1)) ∧ (p3 ∨ p5)) ∨ True)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41794068263211213771686575443 : (((((True ∧ p1) → (p5 ∨ True)) → ((p2 ∨ (((p5 ∨ p4) → (p5 ∧ p1)) → (False → p2))) ∧ (p3 ∨ ((False ∨ p2) → p3)))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677369305475792754673364787348 : ((((((((((p4 ∧ (True ∧ p3)) ∧ (p4 → (p4 ∨ p2))) ∧ p1) ∧ p1) ∨ (p2 ∧ p4)) ∧ p3) ∨ p4) ∨ ((False → p5) ∨ (True ∨ False))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_609515870818864137830460079636 : (((((p2 ∧ (((p3 ∨ (True ∨ ((p5 → p2) ∨ (p2 → p4)))) → ((((p1 ∨ False) → p5) → p1) ∨ (False ∧ True))) → p2)) ∨ p4) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323575470312711832747866822258 : (p5 ∨ (((p2 ∧ p2) ∧ ((((p2 → False) ∧ (p1 ∨ ((((p1 ∨ True) ∧ p5) → p5) ∨ (False → True)))) ∧ p4) ∨ p1)) → (p1 ∧ (True ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
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
      exact h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h14 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h15 := h9 h14
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h17 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h18 := h9 h17
        -- False on the left can always be used.
        apply False.elim h18
  case inr h19 =>
    -- One of the premise coincides with the conclusion.
    exact h19
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h20.left
  let h23 := h20.right
  -- Disjunctions on the left can always be decomposed.
  cases h21
  case inl h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- Conjunctions on the left can always be decomposed.
    let h27 := h25.left
    let h28 := h25.right
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h29 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h32 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h33 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148111091946276342906116469130 : ((((p5 → (((p2 → (False ∧ p3)) ∧ (p2 → p2)) → True)) ∨ (True ∨ ((p2 → False) → True))) → (False ∧ p2)) ∨ (((p5 → True) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324176674949593512572715083310 : (p5 ∨ (((p4 ∨ p1) → (p5 → (p5 → ((p3 → True) → p2)))) ∨ (p1 → ((True ∨ ((p1 → False) → (((p4 ∨ p2) ∧ p1) ∨ p2))) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2201875966470290206106297356 : ((p2 ∨ (((p4 ∨ p5) → (p1 ∧ (((p1 → p3) ∨ p2) ∧ p1))) ∨ (p4 ∨ p3))) ∨ ((p5 ∧ (False → (p2 ∧ p5))) → (True ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324737852364557075089757804215 : (p5 ∨ ((p2 ∧ (p4 → p4)) → ((True → ((p4 ∧ (p1 → (False → (p2 ∨ p2)))) ∧ (p4 ∧ (p4 ∧ True)))) ∨ (p2 → (p5 ∨ (True ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55450140059356465351278211057 : ((((True ∧ (False ∨ (p3 → p5))) → False) → (((p5 ∨ ((True ∧ p3) → (p3 ∧ ((((p1 → False) ∨ p1) → p3) ∧ p2)))) ∨ p5) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32931554270373936398786867232 : ((p3 ∨ (((p5 → p2) ∨ (p3 ∨ ((p2 ∨ (True → ((p5 ∧ (((p1 → False) → p2) ∨ p4)) ∨ p2))) ∨ (p1 ∧ p1)))) ∨ (False → p1))) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726092234394712433302386971779 : (((((p1 ∧ p3) ∨ p2) ∨ ((((p2 ∧ (p2 ∧ p2)) ∧ ((True ∧ p2) ∧ p4)) ∨ (((True ∨ False) ∨ p4) ∧ (p2 → p2))) → (True → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208649699485669103950240582476 : ((True ∧ (True ∨ (p1 ∨ (True → True)))) → (((p3 ∧ (p3 ∧ (p2 ∨ False))) → (((p4 ∧ p5) → p4) → (p5 ∨ p1))) ∨ (p4 ∨ (p2 → True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210524683130215589913703936374 : ((((True ∧ p4) ∧ p3) → p3) ∧ ((p1 ∧ ((p1 ∧ ((p2 ∨ (p4 ∧ ((p4 ∧ False) → (p3 → p4)))) ∧ p5)) → (p2 ∨ (False ∨ p2)))) ∨ True)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608286500925746748621829441499 : ((((((((p1 → (p4 → ((p5 ∨ True) ∨ (((p2 ∧ p1) ∨ p2) ∨ False)))) ∨ ((p5 ∧ p2) ∧ False)) → (p2 → p4)) ∨ p4) ∨ p5) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_191856756081576568350716259343 : ((p4 ∨ ((((p2 ∨ (p4 → True)) ∨ True) → p4) ∧ False)) ∨ (p2 → (((p2 ∨ (p5 → p2)) ∧ (p1 → True)) → (p2 ∨ ((p4 → True) → p4))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208951482916325407815434601055 : ((True ∨ ((p1 ∧ (False ∧ False)) ∨ p4)) → ((True → False) → (((((False → (False ∨ (p2 → p4))) ∨ (p5 ∨ True)) ∧ p3) ∧ p2) ∨ (True ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h12 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h14 := h2 h13
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9080844125945050726452851421 : ((((True ∨ (((p3 ∧ p1) ∧ ((p1 ∨ ((True → p1) → p1)) ∧ p1)) → p4)) → (((((p2 → p1) ∨ p4) → p5) → p1) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255848893502501079136860666512 : ((True ∨ p1) → (((p4 ∧ ((True ∧ (((p3 → False) ∧ p4) ∨ ((False ∧ p3) ∨ True))) ∧ ((p3 ∧ False) → (p1 ∧ p4)))) ∧ (p1 ∨ p3)) ∨ True)) := by
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
theorem thm_5_vars_200162329259542989950649581526 : ((((p2 → False) ∨ p4) ∨ ((p3 → p3) ∧ p4)) → (p3 ∨ (((((p3 ∨ True) → False) ∧ (p3 → p1)) ∨ ((p3 → (p2 → p3)) ∧ p3)) → p3))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h8 : (p3 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h9 := h6 h8
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
        have h18 : (p3 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h16, we can now drive its conclusion.
        let h19 := h16 h18
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- One of the premise coincides with the conclusion.
        exact h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h26
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
      have h30 : (p3 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h28, we can now drive its conclusion.
      let h31 := h28 h30
      -- False on the left can always be used.
      apply False.elim h31
    case inr h32 =>
      -- Conjunctions on the left can always be decomposed.
      let h33 := h32.left
      let h34 := h32.right
      -- One of the premise coincides with the conclusion.
      exact h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622262228599863665463871958100 : ((((p3 ∧ ((((((p2 ∧ p2) → (p3 ∨ ((p4 → p3) → (True ∨ False)))) → ((p1 ∧ p4) ∧ False)) ∨ (p3 ∧ p2)) ∧ p3) ∧ p4)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604370535183755542013740955642 : ((((True → ((True ∧ p3) ∨ (((p3 → (((p2 ∨ ((False ∧ True) ∨ p5)) ∨ (p1 ∨ (False → p5))) → p1)) → (p3 ∧ p3)) ∧ p2))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352137826748364338653713253587 : (p4 → ((((p4 ∧ p2) ∧ (True ∧ p1)) → p3) → ((p1 ∨ p4) ∧ (((p4 → True) ∨ p5) → ((p3 → True) ∧ ((p3 ∨ True) ∧ (p1 ∨ p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48602591199004565433518487337 : (((((p3 ∧ ((False ∧ (p2 ∧ p4)) ∨ p2)) ∧ (((p3 ∧ False) ∧ ((p2 ∧ p3) → p4)) ∧ False)) ∨ (False ∧ p4)) ∧ ((False ∨ p5) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138066329919713011046183869083 : ((True → (p5 ∨ (p1 ∧ ((p3 ∧ (((p4 ∧ (True ∨ (p1 ∨ ((p4 ∧ (p2 ∧ p4)) ∨ False)))) ∨ True) ∧ p5)) ∧ p3)))) ∨ ((p5 → p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145879128494911102549841893120 : (((p3 ∨ p5) → (((False ∧ (((False ∧ p1) ∧ (p4 → (p4 ∨ p5))) ∧ p2)) ∨ ((p2 ∧ p5) ∨ p4)) ∨ True)) ∧ ((p3 ∧ (False ∨ False)) → p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122642644564456873487249014256 : ((((p1 ∨ ((False ∧ (((False → p4) → True) ∧ ((p1 → p1) ∨ ((p3 ∧ False) ∨ p1)))) ∧ p3)) ∨ (p3 ∧ p1)) → (False ∧ p5)) → (p5 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46851783466577389513350010586 : (((((False ∨ False) ∨ ((True → ((((p4 → p2) → p4) → (p5 → ((True → False) ∨ False))) → (p2 ∨ p4))) ∧ True)) ∧ p4) ∨ (False → False)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341042554134825193744950894537 : (p2 → ((False ∨ ((False → ((((((p1 → (p5 → p5)) → (p3 ∧ p4)) → p4) ∨ ((p1 → False) → p3)) ∧ p3) ∧ p2)) → (p3 → p1))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308489906440511695698670615045 : (p2 ∨ (((p2 ∨ (((p3 ∨ True) ∧ ((p2 ∧ (p1 → True)) → (True ∧ (p5 ∧ (p4 → (p1 → p3)))))) → p1)) ∨ (False → (False ∨ p5))) ∨ False)) := by
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
theorem thm_5_vars_117582651036716160614114900075 : ((p2 ∧ (True ∧ (((((p3 ∧ (p1 ∨ (p3 ∧ (p4 → p2)))) ∨ p3) → ((p5 ∨ p3) ∧ p1)) ∨ ((p2 ∨ True) ∧ p1)) ∧ p3))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719604972864212041365671390534 : ((((p4 ∨ (p5 → (p1 ∧ p4))) ∨ (p4 ∧ (((p3 ∧ False) ∧ True) ∨ ((((p2 ∨ p2) → (True → p3)) → (p2 ∧ (p4 ∧ p5))) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684324528753611192826188698217 : ((((((p4 → p1) → (False → ((False → (p4 ∨ (False ∨ p4))) → p3))) → ((p3 ∨ p1) ∨ False)) ∨ (p4 ∨ (p2 ∧ ((False → p3) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212709912773474251961249713843 : ((False → (p2 ∧ (p1 → p4))) ∧ (((p4 → p2) ∨ (((((((p2 ∧ True) ∧ (p1 ∨ p2)) ∧ p2) ∧ p3) → p2) → (True ∧ p1)) ∨ True)) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620294871624834398695705496781 : (((((False ∨ p1) ∨ ((True ∨ p2) → (((False → True) ∧ (p3 ∨ True)) ∧ ((False ∧ p3) ∧ (p1 ∨ ((p1 ∧ True) ∧ (p4 ∧ p5))))))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_253746032329774284982234385440 : ((p1 ∧ p1) → (((((p4 ∧ p1) ∨ (p1 ∨ ((p3 ∨ p1) → p5))) → True) ∨ p3) → (p5 → (p5 ∧ (((True ∧ p4) → (p5 → p3)) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h1.left
    let h15 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122264865160278810960557862197 : ((((True ∨ False) → (p1 ∧ ((((p1 → (p4 ∨ p3)) ∨ ((True → (True ∧ p3)) → p5)) ∧ p4) ∨ (p4 → p2)))) ∧ (p3 → p1)) → (p5 ∨ True)) := by
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
theorem thm_5_vars_351928351068834352540077258374 : (p4 → ((((True ∧ ((p3 → True) → (p5 ∧ p4))) ∧ p1) ∨ True) → (False ∨ ((p1 ∨ (p2 → ((False ∨ False) ∧ (False ∧ p2)))) ∨ (p4 ∨ p3))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60202889437995376160255320484 : (((p5 ∨ p5) → (True ∧ ((((((p3 ∨ p2) → ((p3 ∧ p2) ∨ False)) ∨ (True ∨ (p3 ∧ (p2 → p4)))) ∨ (p1 ∨ True)) ∨ p3) ∨ False))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
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
theorem thm_5_vars_187084275792042395363906063460 : (((p1 → False) ∧ (((p1 → p5) → ((False → p1) ∧ p2)) ∨ p4)) → (((True ∨ (p3 ∨ True)) → p2) ∨ ((((p5 ∨ p3) ∧ False) → p1) ∨ p5))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113505584131879971875574873219 : ((((((p2 ∨ p2) ∧ (p4 → ((p5 ∧ p5) → (False ∧ p2)))) ∨ (p4 ∧ p3)) ∨ (p3 → ((p5 ∧ False) → True))) ∨ (p5 → p3)) ∨ (p4 ∧ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133660109388309049177878955688 : ((((((p3 ∨ (p4 ∨ p2)) ∨ False) ∨ (((True → ((p3 → p1) ∨ p2)) ∨ p4) ∧ (True ∨ p2))) ∨ (p2 ∧ p3)) ∧ p4) ∨ (p4 ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185377970334503857016071122510 : ((p5 ∧ ((p1 ∧ (p3 → (p4 → (True ∨ p1)))) → (p1 → False))) ∨ (p1 → ((p5 → False) → ((p2 ∨ ((p5 ∧ p4) ∧ p4)) → (p5 → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751667336556577927988725498002 : (((True ∧ (p3 ∧ (p2 → (((p5 ∧ (p2 → ((True ∨ p2) ∧ ((False → True) ∧ (p1 ∨ ((False ∨ p5) ∨ False)))))) ∨ (p2 ∧ p1)) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655558384974727624903870706076 : (((((((((False ∨ p1) ∧ ((p4 ∨ p5) → False)) → p4) ∨ p5) ∨ (p4 → ((p2 → p1) → (p2 ∨ True)))) → (False ∧ False)) ∨ (p5 ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



