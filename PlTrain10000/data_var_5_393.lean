variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124337108921503376187681371683 : (((False → (p3 ∨ (((p2 → False) ∧ p1) ∧ p4))) ∧ ((p4 ∨ (p5 ∧ ((p5 → True) ∧ ((p5 ∨ False) ∨ p3)))) ∧ (True → p3))) → (False ∨ p3)) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h17 := h5 h16
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- False on the left can always be used.
        apply False.elim h18
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103090675664098869828681240606 : (((((p2 ∨ p3) ∨ p2) ∧ (((False ∧ (p2 → p4)) ∧ False) ∧ ((((p5 → (p1 ∨ p1)) ∧ (True → p1)) ∧ p4) ∧ p1))) ∨ True) ∧ (p5 → True)) := by
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
theorem thm_5_vars_118605786284271152808222141535 : ((p4 ∨ (((p3 → True) → ((((p2 ∧ True) ∨ ((p4 ∧ (p4 → p5)) ∨ p2)) ∧ (p4 ∨ p3)) → p3)) ∨ ((True → p2) → p2))) ∨ (p5 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608477451501304695039529282469 : (((((((p4 ∨ (((p4 ∧ (p2 ∧ (p3 ∨ (p1 ∨ ((p3 → True) → p5))))) ∧ p1) ∨ False)) → (p1 ∨ (True ∧ p5))) → p4) ∨ p3) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115135871076087036316169020772 : ((((p4 → p5) ∧ (((p3 ∨ p5) ∧ ((True → p5) ∧ p2)) → p1)) → (((False ∨ False) → p4) → (p1 → ((p4 → p3) ∨ True)))) ∨ (p1 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165655404125812355778694736759 : (((((p2 → p5) ∧ p5) ∧ (p5 → False)) ∨ (p5 → (True → (False ∧ (False ∧ (p5 → p5)))))) ∨ ((p5 ∧ ((p5 ∨ p2) ∨ True)) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241719106899243627294740614859 : ((p1 → True) ∧ (((False → p1) ∨ ((True ∨ (p1 ∧ True)) ∨ ((p2 → ((p1 → p5) ∨ True)) ∨ p2))) → (((p2 ∨ p3) → p5) ∨ (False → False)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- False on the left can always be used.
        apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44591607627820814216031824945 : ((((p2 → ((False ∨ (p1 ∧ p1)) ∨ (p1 ∧ p1))) ∨ ((p5 ∧ (True ∨ ((True ∨ True) ∨ (p3 → (p5 ∨ (False → False)))))) → p4)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324198771327128861151944371283 : (p5 ∨ (((((p5 ∧ True) → p2) ∨ (True ∨ p5)) → (p5 ∧ p4)) → (p5 ∨ (((((p4 → (p4 → p2)) ∨ False) ∨ p1) ∨ p1) ∧ (p5 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∧ True) → p2) ∨ (True ∨ p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113591046283387505430864261233 : (((p4 ∧ (p1 ∧ (False ∨ (((p4 ∧ ((((False ∧ p2) ∧ p5) ∨ (p5 → p4)) ∨ True)) ∨ (p2 → False)) → p1)))) ∨ (p1 ∧ p2)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319212500932051320238334954229 : (p4 ∨ (((p1 → (p4 ∨ (p1 ∧ True))) → (((True → (p2 ∧ (True → (p2 ∨ p5)))) ∧ p2) ∧ p1)) → ((p1 ∧ ((p2 ∧ p4) ∨ p2)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → (p4 ∨ (p1 ∧ True))) := by
    -- Implications on the right can always be decomposed.
    intro h3
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (p1 → (p4 ∨ (p1 ∧ True))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h6
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62130017853411911103813481887 : ((p2 ∧ (p4 ∨ (((p3 ∨ ((p1 → (p4 ∨ p2)) ∨ (((p4 ∧ (True ∨ p2)) ∨ (p5 ∧ True)) ∧ p2))) ∨ (p1 → (p3 → p4))) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737585977744724475674623663291 : ((((p5 → p1) ∧ (p5 ∧ ((p4 → ((p2 → (p4 → (False ∧ p5))) → p2)) ∨ ((True → ((p3 ∧ False) ∧ (False → (p2 → p1)))) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193158811570266894696123441919 : (((False → ((p2 ∧ p5) ∧ p1)) ∨ (p1 ∧ (False → p5))) → (False ∨ (p5 ∨ (True ∨ ((p5 → (p1 ∨ p5)) → ((p1 ∧ True) → (p5 ∨ p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136823084162962830121449698682 : (((True ∧ p3) ∨ (((False → (p1 → (((p5 → p2) ∨ p4) ∨ False))) → ((p3 ∧ False) ∧ (p1 ∨ p2))) ∨ (p4 → p3))) ∨ ((p2 → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43851872993476585211343278977 : (((((True → (((p5 ∨ ((True ∨ (p1 ∧ (p4 ∧ True))) → p4)) ∨ p5) ∨ (p2 → (p1 ∧ p1)))) → (True ∧ True)) ∧ (p1 → True)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689648438624110082888896275171 : ((((((p5 ∨ p3) → (False ∨ False)) ∧ ((False ∨ (((p4 ∧ False) → False) ∧ True)) ∧ p1)) ∨ ((False → p3) ∨ ((p5 → (False ∧ p2)) → p4))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_2974800235891684735180331607 : ((p4 ∨ (False ∧ False)) ∨ (((p5 ∨ (p2 ∨ ((False ∧ p3) → (p1 → (p3 ∨ p3))))) ∧ (((p4 ∨ p5) → (p4 → p4)) ∨ p2)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208910103635121342580942328928 : ((p5 ∧ (((p1 ∨ False) → p2) → p4)) → ((True → (((True ∧ p3) ∨ p3) ∨ ((p2 → p3) ∨ p5))) ∨ (((p5 ∨ p3) ∧ True) ∧ (p2 ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37750676673002466767683741729 : (((((((p4 → True) → False) ∨ (p4 ∧ False)) → (p3 → ((p5 ∧ (p4 → (p4 ∧ p1))) → (((False → False) → True) → False)))) → p4) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310309390837986048101738226231 : (p2 ∨ ((p2 ∧ (((p5 ∧ ((p3 → p4) ∧ True)) ∨ p4) ∨ False)) ∨ (p2 → (p5 → (((p4 → True) → (p1 ∧ (p5 → (p3 ∧ p3)))) ∨ p2))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329517767483409006315417879156 : (True → ((p1 ∧ True) ∨ (p1 ∨ ((False ∨ (p3 ∧ (((p2 ∨ p4) → p2) ∧ (((p1 → (p2 → p3)) ∧ p4) ∨ (p1 ∨ p4))))) ∨ (p5 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134081722747310178812636103785 : (((((((p4 → (p3 ∨ (p4 ∧ p3))) → p1) ∨ p3) ∨ ((((False ∨ p3) → (p1 ∨ p1)) ∧ p5) ∨ p4)) → p4) ∨ p1) ∨ (False → (p1 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308467313561855214414261648006 : (p2 ∨ (((p5 → (p1 ∨ (((((p1 ∨ ((p2 ∨ p5) ∨ (p4 ∨ True))) ∧ p5) ∧ p2) → p4) ∧ ((p4 → p3) ∨ True)))) ∨ (p1 ∨ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197493904744344395257994569114 : (((p3 ∧ ((p5 → p5) → False)) ∧ (p5 ∨ p1)) ∨ (p2 → ((False → ((((p4 → (p3 ∨ False)) ∧ False) → (p1 ∧ (p1 ∨ p4))) → False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112206981014739118009535031895 : (((False ∨ (((p4 ∧ (((True ∧ p3) ∧ ((p1 → ((p5 ∧ ((True ∨ p4) ∧ p5)) ∧ p1)) ∧ True)) ∨ p5)) ∨ p2) ∨ p4)) ∨ True) ∨ (True → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768443071305186838397714939656 : (((p5 ∧ (((p4 ∧ (p2 ∧ (p3 ∨ (((p1 ∨ p2) ∧ p4) ∧ p3)))) ∨ ((p5 ∨ (True ∨ p3)) ∧ p2)) → ((p1 ∧ False) ∧ (p5 → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342187507582200095737161348068 : (p2 → ((((True ∧ (p4 → p2)) ∨ (((p4 ∨ (p3 ∧ p2)) ∨ p2) ∧ (False ∨ ((p2 ∨ p3) ∨ False)))) ∧ p1) → (p5 ∨ (False → (p2 → p1))))) := by
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
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h8
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h15 =>
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- Disjunctions on the left can always be decomposed.
            cases h17
            case inl h18 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h19
              -- Implications on the right can always be decomposed.
              intro h20
              -- False on the left can always be used.
              apply False.elim h19
            case inr h21 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h22
              -- Implications on the right can always be decomposed.
              intro h23
              -- False on the left can always be used.
              apply False.elim h22
          case inr h24 =>
            -- False on the left can always be used.
            apply False.elim h24
      case inr h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h28 =>
          -- False on the left can always be used.
          apply False.elim h28
        case inr h29 =>
          -- Disjunctions on the left can always be decomposed.
          cases h29
          case inl h30 =>
            -- Disjunctions on the left can always be decomposed.
            cases h30
            case inl h31 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h32
              -- Implications on the right can always be decomposed.
              intro h33
              -- False on the left can always be used.
              apply False.elim h32
            case inr h34 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h35
              -- Implications on the right can always be decomposed.
              intro h36
              -- False on the left can always be used.
              apply False.elim h35
          case inr h37 =>
            -- False on the left can always be used.
            apply False.elim h37
    case inr h38 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h39 =>
        -- False on the left can always be used.
        apply False.elim h39
      case inr h40 =>
        -- Disjunctions on the left can always be decomposed.
        cases h40
        case inl h41 =>
          -- Disjunctions on the left can always be decomposed.
          cases h41
          case inl h42 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h43
            -- Implications on the right can always be decomposed.
            intro h44
            -- False on the left can always be used.
            apply False.elim h43
          case inr h45 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h46
            -- Implications on the right can always be decomposed.
            intro h47
            -- False on the left can always be used.
            apply False.elim h46
        case inr h48 =>
          -- False on the left can always be used.
          apply False.elim h48



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317932763560517393417869910662 : (p4 ∨ ((p1 ∨ ((True ∧ (((p4 → p4) ∨ (p4 → p3)) ∧ ((((False ∨ p2) → p1) ∨ p1) ∧ ((p3 ∧ p2) ∨ p1)))) ∨ (p3 → p3))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_208562294058694056269259206855 : (((p4 ∨ p3) → ((False ∧ p3) ∧ p2)) → ((((p2 → p4) ∨ (p1 → p5)) ∨ (((p2 → p2) ∧ (p2 ∧ p1)) ∨ (False ∧ p5))) → (p5 ∨ True))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52124931261704164832425251256 : ((((False ∨ (((((p4 → p4) ∧ (p5 ∧ p5)) ∨ p2) ∧ p2) ∨ (True ∨ p3))) → True) → (p1 ∨ ((False ∨ ((True → False) ∨ p4)) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633867014124839833603983369155 : (((((((p5 ∨ (p4 ∧ (False ∧ ((False ∧ (True → p3)) → ((True ∨ p2) ∨ (True → (False → p5))))))) ∧ p5) ∨ p4) → (p1 → p1)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207878311357790942805314119826 : ((((p3 ∧ p3) → p2) ∧ (p1 → p4)) → ((((p2 ∨ False) ∨ ((p1 ∨ ((p2 → (p2 ∨ p5)) → p1)) → p1)) ∨ p5) ∨ ((True ∨ True) ∨ True))) := by
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
theorem thm_5_vars_117126660436374042439200683334 : (((p4 → p2) → ((((True ∨ (False → p1)) ∨ ((p1 → ((p4 ∧ p1) ∨ p5)) ∨ True)) ∧ p1) ∨ ((p1 → (False ∨ p4)) ∨ False))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310290169095725248767023207731 : (p2 ∨ (((p2 ∨ (False ∧ ((p4 → (p1 ∨ p2)) ∧ True))) ∧ p4) ∨ (True ∧ ((p2 ∧ (p3 ∧ ((p3 ∨ True) → ((True ∨ p1) ∧ p2)))) ∨ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38754625559648411671264285867 : (((((True ∨ False) ∨ (p4 → p5)) ∧ (p4 → ((((p4 ∧ p2) ∧ (p2 ∧ p4)) ∧ ((p3 ∨ (p4 ∧ p3)) ∨ (True → False))) ∨ p5))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328993898209751960405620977572 : (True → (((False ∨ p5) ∧ ((p2 ∨ p4) ∧ p3)) ∨ (p1 → (p5 → ((False → True) ∨ (((p1 ∧ p4) ∨ (True → p2)) ∨ ((p2 → p2) → p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317891245599063369235113025733 : (p4 ∨ ((False ∧ (p1 → ((False ∨ p4) ∧ ((False ∨ (p2 ∨ (((((p5 ∧ p2) ∨ p2) ∧ False) ∧ True) → p4))) ∨ ((p5 ∨ p5) → True))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166223072444118892987490854967 : ((p2 ∧ (((p2 ∨ p3) ∧ (((p4 → p5) ∧ p4) → ((True → False) → True))) → (False ∧ True))) ∨ (((p3 ∧ p5) → p3) ∧ (p3 ∨ (p1 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179167417829965982671996906031 : ((p2 ∧ (p2 ∧ ((((p2 ∧ p2) → ((p4 ∨ p3) → p1)) ∨ False) → p5))) ∨ (False ∨ (True → ((False ∧ (False → p4)) ∨ ((True ∨ True) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_179302901284708288935402560589 : ((False ∨ ((p2 → (((p4 ∧ p4) ∧ (False ∧ p4)) ∨ p3)) ∨ (p3 ∧ False))) ∨ ((False ∨ (((p3 ∧ p4) ∨ p1) ∨ p2)) → (False → (p3 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336504385798638984470183686870 : (p1 → (((((p1 ∧ p3) ∨ ((p5 → (p5 ∧ ((((p1 ∨ (False → (False ∧ p4))) → False) ∨ p1) ∨ p3))) ∨ True)) → (p3 ∧ False)) ∧ p1) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((p1 ∧ p3) ∨ ((p5 → (p5 ∧ ((((p1 ∨ (False → (False ∧ p4))) → False) ∨ p1) ∨ p3))) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136031233618988506124364168375 : ((((p2 ∨ (p1 → p1)) → ((p4 ∨ p4) ∨ (p1 ∧ p3))) → (((p2 ∧ ((p2 → p4) ∧ (p5 → p1))) ∨ True) ∨ p1)) ∨ (p2 ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308535821698218295418638999913 : (p2 ∨ ((((p2 → False) → (p1 ∧ ((p3 ∧ (p4 ∧ False)) ∧ (True ∨ p4)))) ∨ (p5 ∧ (p4 → ((False ∨ ((p3 → False) ∧ False)) ∧ p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609545310648290774734150364225 : (((((p3 ∧ (((False ∧ (False ∧ (((p2 → (p5 ∨ (False ∨ (True ∨ p1)))) → p2) ∨ True))) ∨ True) ∨ (p1 → (p1 ∨ p3)))) ∨ True) ∨ p5) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_248794423186618872110126336799 : ((p3 ∨ p3) ∨ (p2 → (p3 ∨ ((p4 ∧ (p2 → (p4 ∨ ((p5 → (((p4 → p1) → False) → p1)) ∧ p5)))) ∨ (p5 → ((True → p5) → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339025410298399050382758606140 : (p1 → (True ∧ ((p3 → (False ∨ p1)) ∧ (((p3 ∨ False) ∨ ((p5 → False) → (((p1 → p5) ∨ ((p3 ∧ False) ∨ p1)) ∨ p2))) ∨ (False ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345366837267062133912776698395 : (p3 → ((((p2 → ((p1 → p3) ∨ ((((p5 → p3) ∨ p1) → ((p4 → p5) ∨ (True → p2))) ∧ False))) → ((p4 ∨ p4) ∧ p5)) ∨ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351253233543209150437829804783 : (p4 → ((True ∧ ((True → (p5 → p4)) → (p2 → (False ∨ (p3 ∧ ((True → (p4 ∨ (False → p2))) → (p1 ∧ True))))))) ∨ ((p4 ∨ False) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256066506839058089917293227586 : ((True ∨ p4) → ((p5 ∧ True) → (((p1 → (p4 → ((((p2 ∨ (p5 ∧ (p4 ∨ p4))) → p2) → p2) ∨ (True → False)))) ∨ p4) ∧ (p3 ∨ True)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : (p2 ∨ (p5 ∧ (p4 ∨ p4))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h2.left
  let h13 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310489795030521108473195287005 : (p2 ∨ (((p3 ∧ (p4 ∨ (False ∨ p4))) ∨ True) ∨ ((p1 ∧ p4) ∧ ((p5 ∧ ((False → (p1 ∧ (p1 ∨ p1))) ∨ ((False ∧ True) ∧ p1))) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32636811568068824497835024599 : ((p2 ∨ ((p1 → (p4 ∨ p2)) ∨ (((False ∨ ((p2 ∧ p5) ∧ ((True ∧ (p5 ∧ p4)) ∧ True))) ∧ p3) ∨ (True → ((p1 → True) ∨ p1))))) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197882580544361444839451810668 : ((((p2 → p3) ∨ p1) → (p3 ∨ (p4 ∨ p2))) ∨ (((((p4 ∨ True) → (p3 ∧ (False → False))) ∨ (p1 ∧ p3)) → ((p1 → p3) ∨ p3)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (p4 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- We need to get the left conjuct of h4 based on <expert-advice>.
    let h5 := h4.left
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44315686030052651872665784819 : ((((((p2 ∨ (((p1 → p5) ∧ (True → p5)) → p4)) → False) → (p4 ∨ (False ∧ p4))) ∨ (((False ∨ p5) → p1) → (p4 ∨ True))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118413671992035570723362011929 : ((p2 ∨ (p1 ∧ (p1 ∨ (((((p5 ∨ p5) ∨ p2) ∧ False) → p4) → (p1 ∨ (((((p4 ∧ False) ∧ p1) ∨ False) ∧ p1) ∧ p4)))))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208065504789957668114470759111 : (((p4 ∨ (p5 ∨ p3)) ∨ (p1 ∨ p1)) → (((((p2 → (p4 → p2)) ∧ (p1 ∨ (False → False))) → (p3 ∨ p1)) ∨ (True ∨ (False ∧ True))) ∨ p1)) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58715900914328981599281754385 : (((p3 → False) ∧ ((p5 → (((p3 → False) ∧ (p1 ∨ p4)) → ((p1 ∨ ((p3 → ((p3 ∨ (p5 → p3)) → p1)) ∨ False)) → False))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354740692970113602376431333614 : (p5 → (((p3 → ((((p2 ∨ p1) ∧ (p2 ∨ p5)) ∨ (((False ∨ False) ∧ p5) ∨ (p2 → True))) ∨ p3)) → (((p2 ∧ True) → p1) ∨ True)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135345721399387386520816489394 : (((False ∧ (((False → (p2 ∧ p2)) ∧ (p2 ∧ (False ∧ p4))) ∨ (((p3 → p2) → p2) → p4))) ∧ (True ∨ (p1 → p1))) ∨ (True ∨ (p4 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340168314011930178242680216355 : (p1 → (p4 → (((((True ∨ (p3 → p5)) → ((False ∨ p2) ∧ p1)) ∨ (p2 ∧ False)) ∨ (p4 ∨ p2)) ∧ ((False ∨ False) → (p1 → (p1 ∨ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246069730357069759382788541562 : ((p4 ∧ p1) ∨ ((((((True ∧ (False ∨ p1)) ∧ ((((p3 ∧ p1) → (False ∨ (False → p3))) → p5) → (False → p4))) ∨ p3) ∧ p1) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178078716720774891207837308373 : (((((((False ∨ (True ∧ p4)) ∧ (True ∧ True)) ∨ p2) ∨ False) → False) → p4) ∨ (((p2 ∨ ((p2 → ((p2 ∨ p4) → False)) → p4)) ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258404822776124924700174696740 : ((p5 ∨ p1) → (((((p4 → True) → (p3 ∧ False)) ∨ (p1 ∨ ((((((p1 → p3) → (p2 ∧ p1)) ∧ p1) ∨ True) ∧ p4) ∨ True))) → p4) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : (((p4 → True) → (p3 ∧ False)) ∨ (p1 ∨ ((((((p1 → p3) → (p2 ∧ p1)) ∧ p1) ∨ True) ∧ p4) ∨ True))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : (((p4 → True) → (p3 ∧ False)) ∨ (p1 ∨ ((((((p1 → p3) → (p2 ∧ p1)) ∧ p1) ∨ True) ∧ p4) ∨ True))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150413198299831120302184227088 : ((((((((p4 → True) ∨ p2) → True) ∨ ((p4 ∨ (True ∨ (p5 → p1))) ∧ p2)) ∧ (p1 ∨ p4)) ∨ p2) ∧ p4) → (p1 ∨ ((p5 ∨ True) ∧ p4))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h6
          case inl h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
            -- One of the premise coincides with the conclusion.
            exact h3
        case inr h20 =>
          -- Disjunctions on the left can always be decomposed.
          cases h6
          case inl h21 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h22 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
            -- One of the premise coincides with the conclusion.
            exact h3
  case inr h23 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122765158043835192508317025055 : (((p2 ∨ ((True ∨ p5) → ((p5 ∨ p4) ∧ (((p4 ∨ (p4 ∨ (False → p3))) → False) ∧ (p4 ∨ (p5 ∧ p3)))))) → (p3 → p2)) → (p3 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793654710766080842874135715040 : (((True → (p5 ∨ (((p5 → p3) ∨ (True ∧ ((p5 ∧ p2) ∧ ((False ∨ (False → True)) → ((p4 ∧ p5) → (p2 → (p5 ∧ False))))))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158638302365451155418020394190 : ((p1 ∧ ((True ∧ (p2 → ((p1 ∨ (p5 → (p4 ∨ (p3 ∨ ((True ∨ p1) ∨ p3))))) ∧ p3))) → p1)) ∨ ((True ∨ p2) ∨ ((False ∧ p5) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188725561769470584036924615884 : ((((p1 ∧ (p4 ∨ False)) ∧ (p5 ∧ p1)) → (p5 → p5)) ∧ ((p5 ∧ ((((True ∧ (p2 ∨ False)) ∧ (p5 ∨ p5)) ∨ p4) ∧ p3)) ∨ (p5 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h4.left
    let h9 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174785919159313521583889661421 : (((p1 ∨ p1) ∧ (p4 ∧ (p4 ∧ (p3 → (True → (p1 ∧ (p2 ∧ (p5 → p3)))))))) → ((p1 → p3) ∨ ((p1 ∨ False) ∨ ((True → p3) → p5)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674477736654372485671988898852 : ((((p4 ∨ (((((p2 → (p1 → True)) ∧ p2) → (True ∧ ((p5 ∨ p2) → (False ∨ p5)))) ∨ p1) → (p2 ∨ p5))) → ((p1 ∧ p4) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53266988117651124183287337613 : (((True ∧ (((p5 ∨ p2) → (p5 ∧ (False ∨ p4))) ∧ (p3 ∨ p4))) ∨ ((((p1 ∧ p2) ∧ (p2 → ((p2 ∧ p3) ∨ p3))) ∧ True) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40382616114013937499473424827 : (((((((((True → (p4 → (False → p2))) → p5) ∨ (p2 ∧ p3)) ∧ (((p3 → p3) → p4) ∨ p4)) ∨ p5) ∨ (p4 → p1)) ∨ p3) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241592626208833465307034782210 : ((False → p4) ∧ ((((p5 → (((p3 ∨ p3) ∧ (p5 ∧ False)) ∨ p1)) ∧ ((False ∧ ((p2 ∧ p3) ∨ p3)) → False)) ∧ p5) ∨ (True ∨ (p1 ∨ False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191648050721415885132009898998 : ((p4 ∧ ((p5 ∧ p2) ∨ (p4 ∨ ((p2 ∨ p3) ∨ p2)))) ∨ ((p5 ∧ p2) ∨ ((True ∨ ((p1 ∨ p5) → ((p4 ∧ p2) ∧ True))) → (True → True)))) := by
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
theorem thm_5_vars_111135346872721774520118633891 : (((((p1 ∧ (p3 ∨ p2)) ∧ (p2 ∨ (p2 ∨ p1))) → ((p4 ∨ (p1 ∨ (False → (p3 → (p5 ∨ (p1 ∧ p4)))))) → p3)) ∧ p3) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55621659101795321863310158535 : (((p4 → (((p3 → p3) ∨ p4) ∧ p4)) → (p1 → ((False ∨ (p2 ∨ ((True → p2) ∧ (True ∨ (p1 ∧ False))))) ∨ ((p1 → False) → p5)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42350445388747104737013641552 : (((p3 ∧ ((((p2 → True) ∧ p5) ∧ p5) ∧ (((p3 → p4) → (p3 ∧ p4)) ∧ ((True → (p1 → (True ∧ p2))) → (p4 ∧ p4))))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_830795090965482195786366497161 : ((((True → ((((p1 ∧ (False ∨ ((p1 ∨ (p2 → p3)) → ((p5 ∧ p4) → p3)))) ∧ (False ∨ True)) ∧ (p2 ∧ p4)) ∧ (False ∧ True))) ∧ p4) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223728051577061203025798193319 : ((p2 ∨ (p2 ∨ True)) ∧ (((((True ∧ p2) ∧ (((p4 ∧ p1) ∨ (p1 ∧ p3)) → (p1 ∨ (False ∧ p4)))) → p1) → (False ∧ (p5 → False))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52633116992208702332892392975 : ((((p4 → p5) ∧ ((((((p3 ∨ p5) → False) → False) ∧ p5) ∧ p3) ∨ p1)) ∨ ((False ∧ p4) ∨ ((False ∨ ((False ∧ True) ∨ True)) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61462432233854585464459963454 : ((p1 ∧ (((((((p3 ∨ (False ∨ p3)) → (((True ∧ p1) → (p3 ∧ p5)) ∧ True)) → True) → p3) ∧ p5) ∧ (False ∧ p1)) ∨ (p3 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206773402333632380300328293812 : ((p4 → ((p2 → (True ∧ p5)) → p3)) ∨ (True → ((((p3 ∧ ((True ∨ (True ∧ p4)) ∧ ((p2 ∧ (p1 ∨ True)) → p2))) → p3) ∨ True) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54719050206793012130091966915 : ((((p1 ∨ ((p4 ∨ True) → False)) → (p4 → False)) → ((((True ∧ p4) ∨ (False ∨ (p5 → p3))) → ((True → False) ∨ (p2 → p5))) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55387326697750836366822267226 : (((((p5 → True) → (p2 ∧ p1)) ∧ p1) → (((p3 → ((((True → True) ∧ False) → (p2 ∧ False)) ∨ (True ∨ p2))) → p5) ∨ (p5 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127505992636244831547969867018 : ((p4 ∨ (((p2 ∧ p4) ∨ ((True ∧ (p3 ∨ ((False ∨ p1) → p3))) ∨ (False ∨ (((p4 ∨ p2) ∧ False) ∧ (p4 ∧ p4))))) ∨ p4)) → (False ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
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
            -- False on the left can always be used.
            apply False.elim h15
          case inr h16 =>
            -- Conjunctions on the left can always be decomposed.
            let h17 := h16.left
            let h18 := h16.right
            -- Conjunctions on the left can always be decomposed.
            let h19 := h17.left
            let h20 := h17.right
            -- Disjunctions on the left can always be decomposed.
            cases h19
            case inl h21 =>
              -- False on the left can always be used.
              apply False.elim h20
            case inr h22 =>
              -- False on the left can always be used.
              apply False.elim h20
    case inr h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133610774803038430675732495820 : (((((p2 → (((((False ∧ p4) ∨ (False → True)) ∨ p1) ∨ (p3 ∧ (False ∧ p1))) → True)) ∧ (p5 → p4)) → p3) ∧ p4) ∨ ((False ∧ p2) → p5)) := by
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
theorem thm_5_vars_305864641107684856868217750962 : (p1 ∨ ((((p4 ∧ (p5 ∨ p1)) ∨ p1) ∨ p4) ∨ ((((p4 → p1) → ((((p5 ∧ True) → (False ∧ p4)) → p3) ∨ True)) → (p3 → p3)) ∨ p2))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133590997493788776392378441196 : ((((p2 ∨ ((p2 ∧ (p4 ∧ p4)) ∧ (((p5 ∨ True) ∧ (((p4 ∧ False) ∨ p2) → (True → p4))) → False))) ∨ p5) ∧ True) ∨ (True ∧ (True ∨ p3))) := by
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
theorem thm_5_vars_670696252499619734918349320109 : (((((p5 → p1) → (((((((p2 ∧ p2) ∨ p1) → (p1 → p3)) ∧ p1) ∨ ((p4 → p1) → p1)) ∨ p1) ∨ p1)) ∨ (False → (p3 ∧ p5))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185835705226191015141322253417 : ((((True → (False ∨ (p2 → ((True ∧ p3) ∧ p5)))) ∧ p5) ∧ p2) → ((p5 ∧ ((True → p5) ∨ p2)) → ((((p1 ∧ p2) ∨ p5) ∧ p3) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h2.left
    let h10 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h1.left
      let h13 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h1.left
      let h18 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h17.left
      let h20 := h17.right
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h2.left
    let h23 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h1.left
      let h26 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h25.left
      let h28 := h25.right
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h1.left
      let h31 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h32 := h30.left
      let h33 := h30.right
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337674554452304005686974655620 : (p1 → ((p3 ∧ ((p4 → ((True ∧ p5) ∧ (p1 → (p1 → ((True ∨ (p1 ∨ True)) → False))))) ∧ p1)) ∨ (((False ∨ (p1 → p4)) → False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106848902160931089449686054309 : (((p5 → (p4 → (p1 → (p5 ∨ p2)))) → ((((((False ∨ (p5 ∨ p3)) → p1) → False) → p4) ∨ ((False → p2) ∧ True)) ∨ p1)) ∧ (p3 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157776616859347298615371717914 : ((((p2 ∧ (False ∨ ((False → (p2 ∨ (p5 → True))) → p3))) ∨ p3) ∨ (p3 ∨ (p2 → (False → False)))) ∨ ((p1 → True) → (p1 ∨ (p1 ∧ p2)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46662918217987034942007944292 : (((False ∨ ((((p4 → False) ∧ p3) → p5) → ((p1 ∧ (True ∧ (p3 ∨ ((True → (p5 ∧ p1)) → (p5 ∧ p1))))) → False))) ∧ (p2 → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158580671749870021136454685476 : ((True ∧ (True ∧ (False ∧ (((False ∨ False) ∧ ((p3 ∨ p4) ∧ ((p5 ∨ (p4 ∨ False)) ∨ False))) ∨ p2)))) ∨ (p5 → (True ∨ (p3 ∨ (p1 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613305750579580262450377550776 : ((((((True ∨ (True ∨ p4)) ∧ ((((((False ∧ p4) ∧ p1) → (True ∧ (p2 → (p1 ∨ p3)))) ∧ p3) ∨ p3) ∨ p3)) → (True ∧ p5)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_17854111246343048494628787648 : (((((((p4 ∧ (p1 ∧ True)) ∨ False) ∧ False) ∧ ((((False → p5) ∧ p4) ∨ p3) → (False ∨ True))) ∨ False) ∨ ((False ∨ False) ∨ (p2 → p2))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680309952344343971681831210684 : (((((p4 ∨ (False ∧ (p5 → (p2 ∨ ((False ∨ ((p2 ∧ p1) ∨ p4)) ∨ p2))))) ∧ (p2 → (True ∧ p2))) → ((p4 ∨ p5) ∧ (p5 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68530840600025182071058489067 : ((p3 → (p1 → ((((((((p4 → p3) → True) → p2) ∨ p1) ∧ p1) ∧ (True ∨ ((p4 ∧ p3) → p3))) ∨ (p4 ∧ p1)) → (True → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147874660238549056685855015975 : (((p4 → (((p2 ∧ ((p4 ∧ p1) → ((p3 → ((p3 ∧ False) ∨ p5)) ∨ p1))) ∨ p5) → (p5 → p2))) → p5) ∨ (True ∨ (p5 ∨ (False → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



