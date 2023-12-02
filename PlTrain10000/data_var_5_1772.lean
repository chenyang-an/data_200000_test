variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41758980202368940137760733841 : (((((p1 ∧ p2) ∧ (p5 ∨ p1)) ∨ ((p5 ∧ ((p1 ∧ (p1 → p3)) → p4)) → ((p2 ∨ p3) → (p3 → ((p5 → p4) ∧ False))))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265560738962557489340600085486 : (True ∧ (False ∨ (True → (((p1 → p4) → ((True ∧ p2) ∧ p1)) ∨ ((((p4 ∨ ((p4 ∨ p3) → p3)) → p3) ∧ False) → (True → (p2 → p5))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154971262203365425956376064207 : (((((p4 → False) → p4) ∨ ((((p3 ∧ (p5 ∨ p5)) ∨ p1) ∨ p1) ∧ p2)) → (p4 ∨ (True ∨ False))) ∧ (p2 → ((p2 → p5) ∨ (p1 → p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- Implications on the right can always be decomposed.
  intro h14
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h15
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111245802170283605384986067807 : ((((p4 → p2) ∧ ((p4 → (p2 ∧ (True → ((p1 ∧ (p4 → p2)) → (False ∨ ((False → (p1 → p3)) ∨ p2)))))) → p1)) ∧ p5) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52818484185488777246069166612 : ((((((p2 ∨ p2) → p1) ∨ True) ∨ ((p5 ∨ p1) ∨ (p3 → (True ∨ p4)))) → ((p2 → ((p3 → (p5 ∨ p4)) → p5)) ∨ (False ∨ True))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166082676195840070289167975766 : (((p3 ∨ False) → (p2 ∨ (((p4 → p4) → (p2 → p1)) → ((p4 ∧ False) ∧ (p2 ∨ p2))))) ∨ (p5 → (((p1 ∨ p5) → False) ∨ (p5 ∨ True)))) := by
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
theorem thm_5_vars_179054422095968986542025979144 : (((p4 → p4) → ((p3 → p5) ∧ ((p1 ∨ p2) ∨ ((p4 ∧ p5) ∨ p2)))) ∨ (((False → False) ∨ (True ∨ (((False ∧ p3) ∧ p5) ∧ p1))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308925364857895325562044278334 : (p2 ∨ (((True ∧ (p5 ∧ (((p4 ∧ ((p4 ∧ False) → p2)) ∨ True) → ((True ∧ (p3 → True)) → False)))) ∧ ((p5 → (p5 ∨ p4)) ∨ True)) → False)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : ((p4 ∧ ((p4 ∧ False) → p2)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : (True ∧ (p3 → True)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h11
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h15 : ((p4 ∧ ((p4 ∧ False) → p2)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h16 := h7 h15
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h17 : (True ∧ (p3 → True)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h18
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h19 := h16 h17
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104521327760360229977484319291 : ((((p5 ∨ (True → ((False ∧ ((p1 → (p2 ∨ p1)) → (p4 ∧ (p2 → ((p1 ∨ p2) ∧ p5))))) ∨ True))) ∨ p5) ∨ (p5 ∨ p1)) ∧ (p1 → p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103140576879383200414814397757 : ((((False → True) ∧ ((((p1 → (p5 → p3)) ∨ p1) → p5) → ((p3 ∧ ((p3 → p2) ∨ p3)) ∨ ((p2 ∨ False) → p2)))) ∨ p4) ∧ (False → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177695048273387387695619590648 : ((((((((p1 → p4) ∨ p2) → p2) ∧ p3) ∨ False) ∨ (p3 ∧ p5)) ∧ p1) ∨ (((False ∧ (p4 → p5)) → True) ∨ (p1 ∧ (True ∨ (False ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160117004776570240536121247219 : (((p4 → ((p3 ∨ ((((p4 ∧ ((True → False) ∨ p4)) → False) → (False → p1)) ∧ p1)) ∨ True)) → p4) → (((p5 → p5) → (True ∧ p4)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → ((p3 ∨ ((((p4 ∧ ((True → False) ∨ p4)) → False) → (False → p1)) ∧ p1)) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147281426045423174398788223516 : ((((True ∧ (((p3 ∧ p1) ∧ p4) ∧ ((p2 → (((p5 ∨ (p2 → p5)) ∨ p3) ∨ p2)) → p3))) ∨ p4) ∨ True) ∨ (((True ∨ p5) → p2) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147751432195021352187672233149 : (((((p4 ∨ p3) ∧ p3) ∨ (p2 ∧ ((p5 ∧ p5) ∨ ((p3 ∨ p4) ∨ ((p4 ∨ (p1 ∧ p3)) ∨ True))))) → p1) ∨ ((p1 → (p5 ∧ p5)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227055152812372059578485539926 : (((p2 ∨ p5) → p3) ∨ (True → ((((p3 ∨ ((p2 ∨ p4) → p5)) ∨ (p2 ∧ ((p5 → ((False → p4) → True)) → (p3 ∧ p2)))) → p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63902948587575724315508489502 : ((False ∨ (((p2 ∨ (p3 → ((p1 ∨ False) ∨ True))) → ((p3 → ((False → True) ∧ p1)) → ((False ∨ (p2 ∨ p1)) ∨ (p5 ∧ p1)))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191679136887486066119686249067 : ((p5 ∧ ((p4 ∧ False) ∧ (((p2 → p2) → False) ∨ p1))) ∨ (((p3 ∧ p1) ∧ (False → ((p1 ∧ p2) → (p2 → ((p5 → True) ∨ p1))))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315837423975709630305326447298 : (p3 ∨ ((True → p3) → (p3 ∨ ((p3 ∨ ((p5 ∧ False) ∧ (((p2 → (p1 ∨ (p5 ∧ p3))) → (p4 ∧ p4)) ∨ p4))) ∨ (p1 ∨ (False ∨ p5)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85877703095166031847933313797 : (((False → ((p3 → ((False → (p3 ∨ False)) → (p1 → False))) ∨ p5)) → (True ∧ ((((p4 ∨ p2) ∧ (p1 ∨ False)) ∨ (False → p2)) ∧ False))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → ((p3 → ((False → (p3 ∨ False)) → (p1 → False))) ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117117301560141920003350671542 : (((p3 → p3) → ((((p5 ∨ p3) ∨ p4) ∨ ((p3 ∧ p3) ∧ (True → p5))) ∧ (((((p3 ∧ p3) → p2) ∧ p4) → p3) → p5))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146989382414064591549923088219 : ((((p1 ∨ (((True → p4) ∨ (p1 → p3)) ∨ ((False ∨ ((p5 → (p4 → False)) ∨ p2)) ∨ False))) → p1) ∧ True) ∨ (False → ((True → p5) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780326746927480390346428201580 : (((p2 ∨ ((False ∨ (((True ∧ (p4 ∨ p2)) ∧ (p5 ∧ True)) → ((p2 → False) ∧ ((p3 ∧ False) ∧ p4)))) ∨ (False → ((p2 ∨ p1) ∧ p2)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590356557755052574818993601766 : (((((((p2 ∨ True) ∨ p2) → ((False ∧ (p4 → p1)) ∨ (((((p1 ∧ (p3 ∧ p4)) ∨ p5) → p2) ∨ (True ∨ True)) ∨ p1))) → p2) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693016289913648996293403041259 : (((((p5 → False) → ((p4 ∨ (((p4 → p3) → p2) → p3)) ∨ (p4 → True))) ∧ ((((True ∧ (p3 ∧ p5)) ∨ (p5 ∧ True)) ∨ p4) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256091779622599478802199690567 : ((True ∨ p5) → ((((p2 ∨ ((False ∨ p3) → p1)) ∨ ((p1 → (p2 ∨ ((p5 ∨ p1) ∨ p3))) ∧ ((p1 ∨ False) ∧ True))) ∧ (p1 ∨ p2)) ∨ True)) := by
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
theorem thm_5_vars_680739937689777659503087416201 : (((((p5 → ((p3 ∧ p5) ∧ p4)) ∨ ((p4 ∧ False) ∨ (((p3 → True) → (p5 ∧ p4)) ∨ (p5 → p2)))) → ((p2 → p4) ∨ (p5 → p5))) ∨ p5) ∧ True) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- One of the premise coincides with the conclusion.
        exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39680416353558774019617948410 : (((p4 ∨ ((p5 ∨ (False ∨ (p5 ∨ (((p4 ∨ (p2 ∨ p4)) ∧ p5) → ((p1 ∧ p1) ∨ ((p4 → True) ∧ False)))))) ∨ (p1 → p3))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723762149565968796938838365623 : (((((p2 → True) → False) ∧ (((p4 → p3) ∧ True) ∨ (p2 → ((p4 → p1) ∧ ((p4 ∨ ((p5 ∨ p2) → (p5 ∧ (p2 ∧ p4)))) ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165461668054532794873185108564 : ((((p3 → False) ∧ (p2 → (p5 ∧ (True ∨ (p3 ∧ p3))))) ∧ ((p2 ∨ p1) ∨ (p5 ∧ p3))) ∨ ((True → (p4 ∨ (False → p5))) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322635851011575081531935654784 : (p5 ∨ ((((((p1 ∨ (p1 ∧ p4)) ∧ (p2 → ((False ∧ False) → True))) ∧ (p5 ∧ ((p4 → p2) ∨ True))) ∧ (p5 → (p5 ∧ p2))) ∧ p1) → p2)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h7.left
    let h12 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h14 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h15 := h5 h14
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h18 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h19 := h5 h18
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- One of the premise coincides with the conclusion.
      exact h20
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h7.left
    let h25 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h26 =>
      -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
      have h27 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h23
      -- We have shown the premise of h26, we can now drive its conclusion.
      let h28 := h26 h27
      -- One of the premise coincides with the conclusion.
      exact h28
    case inr h29 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h30 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h24
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h31 := h5 h30
      -- We need to get the right conjuct of h31 based on <expert-advice>.
      let h32 := h31.right
      -- One of the premise coincides with the conclusion.
      exact h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173784728990450301088141384881 : ((((p4 → p3) ∨ ((p2 ∨ p1) ∨ ((((True ∧ p2) ∨ True) → False) ∧ p3))) ∨ p5) → (((p4 ∧ ((False → p3) → p2)) ∧ (p1 → p3)) ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
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
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260604075721629852901060992620 : ((p3 → p2) → (((p3 ∧ (p3 ∨ (((False → p1) ∨ p1) → ((((p2 ∧ False) → p2) ∨ p3) → p3)))) ∧ p1) → ((p4 → p5) ∨ (p1 → True)))) := by
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
  cases h6
  case inl h7 =>
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
theorem thm_5_vars_190687233945444123318318806921 : (((p5 → (p5 → (((True ∨ p1) ∨ p5) ∨ p2))) → p5) ∨ ((p5 ∨ True) ∨ ((True → (((p1 ∧ (False ∨ p4)) ∧ True) ∨ (p4 ∧ True))) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596832184903346735553848959461 : (((((((p2 ∧ (p4 → p4)) ∨ p5) → p2) ∨ ((p4 → p5) ∧ ((p4 → ((((True → p2) ∨ p2) ∧ p2) ∧ p4)) ∧ (p1 ∨ p1)))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655253025111776383815486910716 : ((((((((True ∧ False) ∨ ((p4 → True) ∧ (p1 → p3))) ∧ p4) ∨ ((p5 ∧ (p1 ∧ True)) ∧ (False ∨ p5))) ∧ (True → p2)) ∨ (True → True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751496587969079523043226367894 : (((True ∧ (True ∧ ((p5 → (p2 ∧ False)) ∧ (p1 ∧ (p4 ∧ ((False ∧ (True ∧ ((p1 ∧ p3) ∨ (p4 ∨ (True → (False ∨ True)))))) ∨ p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47706737490324280059759019568 : ((((((p4 → ((p4 ∧ ((p5 ∧ p3) → p4)) ∨ (p4 ∨ (True ∨ p5)))) ∨ (((p1 → p2) ∨ p5) ∧ p5)) ∧ True) ∨ p3) → (p5 → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184886110728957072137608549519 : (((p3 ∨ (True → p5)) ∧ (False ∨ (((p5 → False) ∨ False) ∨ False))) ∨ ((True ∨ p3) ∨ (False ∨ (((((True ∧ p5) → True) → p5) ∨ p1) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782431211014821406808443653567 : (((p3 ∨ ((((((p3 ∧ (p4 → (p4 ∧ False))) → (False ∨ ((p2 ∧ (True ∧ p2)) → p1))) ∧ p2) ∧ p1) ∧ (p2 ∧ (p5 ∧ p1))) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_147420462745678766685012341002 : (((((p2 ∧ p2) → True) ∧ (p5 ∨ (p1 ∧ ((p2 ∧ ((p4 ∨ True) ∨ (False ∨ p2))) ∨ (False → p4))))) ∨ p1) ∨ ((True → (p2 ∧ p5)) → p2)) := by
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
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642687301542204388006546287810 : ((((p1 ∧ (((p3 ∧ (p5 ∧ p5)) → ((p2 ∧ p2) ∨ False)) → (((p2 ∧ p4) → (((p4 → p2) ∨ False) → (False ∧ p2))) ∧ p4))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354727272906958287119621704769 : (p5 → (((p3 → ((p5 → (p2 ∧ ((p5 ∨ (p4 ∨ p2)) → (p1 ∨ (p5 ∨ ((False ∨ p1) → p4)))))) ∧ p4)) → (p3 ∧ (p3 ∨ p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60572420521646133024161780585 : ((True ∧ (((((p1 → p5) ∨ False) ∧ (p4 → (((p3 → (p4 ∨ p3)) ∧ p4) ∨ (p2 → (p4 ∨ (False ∨ p3)))))) → (p4 → False)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67774387848116271309801468977 : ((p2 → (((p3 → False) → (p3 ∧ (False ∨ ((p3 → (p4 → (p3 ∨ ((p4 ∧ ((p1 ∧ True) ∧ (p5 ∨ p5))) ∨ p3)))) ∧ True)))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169140555691922654561516924003 : ((p5 → (True ∧ ((p5 ∨ (((p3 → p2) → p4) ∨ ((p1 ∨ (p2 ∧ p1)) → p2))) ∨ p1))) → ((True → p4) ∨ ((p5 ∧ p1) → (p2 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181049012913510857538545163569 : (((p1 ∧ True) → ((p1 ∧ (False ∧ p2)) → (((False ∨ p4) ∧ p1) ∧ False))) → ((((p2 ∨ p2) → p4) ∨ (p4 ∨ (p2 ∨ (p3 → p3)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60422682099351005500022109748 : (((p4 → p2) → (p5 ∧ ((True → p2) ∧ (True → (True → ((p4 → ((p4 ∨ ((((p1 ∧ p3) → False) → p5) ∨ p2)) ∧ p4)) ∧ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136874997731482334506390895038 : (((False ∨ p5) ∨ ((False ∧ p5) ∨ (((p3 ∧ ((p3 ∨ p5) ∨ p5)) → ((p1 ∧ p1) ∨ (False → (False → p3)))) ∧ p5))) ∨ (p1 → (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164788170419614660848060585955 : ((((p3 ∧ ((p2 ∧ True) ∧ p1)) ∧ (((p3 ∨ (p5 ∨ (True → True))) → p4) ∨ p2)) ∨ p1) ∨ (p2 → (((False ∧ (p4 → p4)) → p1) ∨ p3))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356703475315753491411179463495 : (p5 → ((p5 ∧ ((True ∨ True) ∧ (p4 ∨ p5))) ∧ (((False ∨ ((p1 ∧ (p4 ∨ False)) ∨ (p2 → (True ∨ p2)))) ∧ True) ∨ ((p1 → p1) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752225631089955700361523286188 : (((True ∧ (p4 → ((((p5 → (p4 ∧ (True ∧ (((p2 ∧ p4) → True) → p1)))) ∨ (True → p4)) ∧ (False ∨ (p5 ∨ (p1 → p5)))) ∨ p4))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355566445521342322891424341681 : (p5 → ((((((p2 ∨ (p3 ∧ p5)) ∧ (p5 ∧ (True → p1))) → ((p4 ∨ False) → p1)) ∧ ((p4 ∧ p3) ∨ p4)) → (p3 ∧ True)) ∨ (p5 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44804559372928594050781202261 : (((((p1 → p2) → p1) ∧ (((p1 ∨ p5) ∧ ((p4 ∧ ((p1 ∨ p5) → (p2 ∧ p2))) ∧ False)) → (False ∧ ((p4 ∨ True) → p5)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652077604823636027263345417313 : ((((False ∧ (p2 ∧ ((((p3 → p1) ∧ p1) ∨ ((p5 → ((True ∧ p4) ∨ (((p2 ∨ p2) → p2) → p2))) → p1)) ∨ False))) ∧ (p1 ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163394640800622192694101242613 : ((((p2 → p2) → (p5 ∨ p1)) ∨ (((p4 ∨ p4) ∧ (False → ((p4 ∧ p2) ∧ p2))) → p4)) ∧ (((False ∨ True) → False) → (p1 ∨ (p1 ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37844849365236446238719755966 : ((((p5 ∨ (((p5 ∧ ((p2 ∧ p5) ∧ (p5 ∨ p4))) ∨ (p1 ∨ (p1 → p2))) → (((p2 ∧ False) ∨ (p5 ∧ p3)) ∨ p2))) → p5) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134996495590543563866258971723 : (((p1 ∧ ((True ∨ (p4 ∧ (p1 → ((False ∧ False) ∧ p5)))) ∧ (p4 ∨ ((True → p2) → (p5 ∧ p1))))) ∧ (p4 → p2)) ∨ ((p2 ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327140214725427944983855768286 : (True → ((p1 ∧ ((p5 ∧ ((p4 → False) ∧ (p2 ∧ (p2 ∧ (p5 ∧ (p1 → (p4 ∧ p5))))))) ∨ (p1 → (False ∧ (False ∧ (True ∨ p2)))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355609616720583731579188899819 : (p5 → (((p3 ∨ p3) → (((True ∧ p4) ∨ (False ∧ (True ∨ p4))) ∨ (p5 ∧ (((p3 ∧ p2) ∨ ((p2 → p2) → p3)) → False)))) ∨ (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173385109473782624444540261068 : ((p4 → ((True ∧ ((p1 ∨ ((True ∨ p1) ∨ p2)) ∧ (p4 ∧ p1))) ∨ (False ∨ p5))) ∨ ((((p3 ∧ (p3 ∧ (p1 → p1))) → p4) ∧ False) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753891715313836664557999855702 : (((False ∧ ((p4 ∨ (p4 ∨ ((p1 ∨ p5) ∧ (p3 ∧ p2)))) ∨ ((p2 ∧ (p5 → p5)) ∧ (True → (p5 → ((p2 ∨ True) ∨ (p3 → True))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140536794369776547587312844068 : ((((((p1 ∨ p1) ∧ ((True ∧ p3) → p5)) ∧ (((True ∧ p5) → False) → False)) ∨ p1) ∨ ((p5 ∨ p5) ∧ (p3 ∧ p4))) → ((True → p4) ∨ True)) := by
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
      let h6 := h4.left
      let h7 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
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
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h13.left
      let h19 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300380965259996275504549985997 : (False ∨ (((True ∨ (p2 → (((p2 → p2) ∧ p4) → (p2 ∧ ((False ∨ False) → False))))) → (((p5 ∧ p5) → p3) ∨ p3)) ∨ (p5 → (False → p4)))) := by
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
theorem thm_5_vars_308728855967825614731672177118 : (p2 ∨ ((p1 → (False ∨ ((True → (((p4 → (p2 ∧ (p5 → (p3 → p1)))) → False) ∧ ((p4 ∨ ((p1 ∨ p2) ∨ p5)) → p2))) ∧ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168256742778458794433311719927 : (((p1 ∨ (p5 ∧ p2)) → ((((p2 → True) ∧ p2) ∧ (((p5 ∨ True) ∨ False) ∧ p4)) → False)) → ((((p2 ∨ False) ∨ (False → p5)) → p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137899509136206412703054959651 : ((p4 ∨ (((((((p3 → True) ∨ p1) ∨ True) → p2) ∧ (p3 ∧ ((False ∧ False) → p4))) ∧ p3) ∨ ((p4 ∧ False) → p2))) ∨ (p3 → (p3 ∧ p1))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39915410753330217733181961071 : (((p3 → ((p3 ∧ (((p1 → (((p5 ∧ p3) ∧ ((False ∧ False) ∨ p5)) ∨ p5)) ∧ ((p5 → p5) ∧ p5)) ∧ False)) ∧ (False → p1))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58072749263997938317312213896 : (((False ∧ p4) ∧ (p5 ∨ (False ∧ ((((True ∨ ((True → p4) ∧ ((p2 ∨ False) ∧ p4))) ∧ True) → (p3 → False)) ∨ (True → (p5 ∧ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321114348525049851012309449066 : (p4 ∨ (p2 ∨ ((p4 → ((False ∧ (((p3 → True) ∨ ((p3 ∨ p4) ∨ p2)) ∨ p2)) ∧ (((p3 ∨ p3) → False) ∧ (p3 ∨ (p1 ∧ p1))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350249653555992459250728743640 : (p4 → ((False ∧ (((p5 ∨ p5) ∧ ((((p3 → p3) → False) → True) ∨ (((p3 → p5) ∧ p1) → p5))) ∨ ((p1 ∧ (False ∨ p2)) ∧ p2))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53344269603222693827999152053 : ((((p2 ∧ (((p5 ∧ p5) ∨ ((p2 ∨ p4) → p3)) ∧ True)) ∧ p2) → ((((p5 ∨ p4) ∨ ((p2 ∨ False) → True)) → p4) ∨ (p3 ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228683664214622194741902634840 : ((p2 ∨ (p1 ∨ p1)) ∨ ((True → (((p2 → ((p3 → (True → (((p3 → (True → p3)) ∧ (True → False)) ∨ p2))) ∨ p1)) ∨ p4) → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683004519431370749391424304477 : (((((p4 ∨ p5) → (p4 ∧ (((p5 → (False ∧ (p5 ∧ (p5 ∧ p4)))) ∧ p4) ∧ (True ∧ True)))) ∧ (p4 ∨ (p2 ∧ ((True → p1) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319357252494300279373105034729 : (p4 ∨ ((((((True → p3) ∧ False) ∨ p4) ∧ (((p3 ∧ p4) ∨ p3) ∨ False)) ∧ p3) ∨ (True ∨ (((p3 ∨ p1) → True) ∧ ((p1 ∧ p4) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263418485542887691907990891313 : (True ∧ ((p3 ∧ ((p3 ∧ (((True ∧ False) ∧ (((p5 → p1) → (((True ∧ p2) ∧ p3) ∨ p4)) ∨ p5)) ∨ p2)) ∨ p4)) ∨ (True ∨ (False ∧ p3)))) := by
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
theorem thm_5_vars_56120318049806743343302532796 : ((((p1 ∨ p5) ∨ (p5 ∧ p2)) ∨ ((p4 ∧ ((p1 ∨ p1) → (p1 → (p1 → (p4 ∧ (p3 ∧ p3)))))) ∨ ((p1 → (p3 → p3)) → True))) ∨ p3) := by
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
theorem thm_5_vars_257062782826421172765356437095 : ((p2 ∨ False) → (((p4 ∨ ((((p2 → p4) → (((p2 ∨ ((p3 ∧ p1) → p2)) → p3) → p1)) ∧ ((p2 ∧ p4) ∧ False)) ∨ p3)) ∨ True) ∨ p3)) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57069171329453348097895850687 : (((p5 → (p3 ∨ True)) ∧ ((((True ∨ (p3 → (True ∨ ((p3 ∨ ((p3 → p2) ∧ (p2 ∧ p2))) → p5)))) ∧ p4) → (False ∧ p2)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42326288564211833374455273893 : (((p2 ∧ (p2 → (((p4 → ((((((p3 ∨ (p1 ∧ (True ∨ p4))) ∧ p4) ∨ (p2 ∨ True)) ∧ p3) ∨ p1) → False)) ∨ False) → p4))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304350836858132587224321857246 : (p1 ∨ (((((((p3 ∧ p5) ∨ p2) → p1) ∧ p2) ∧ p3) ∧ (p3 → (p1 → ((((((False ∧ p4) ∨ False) ∨ p5) ∧ False) ∧ p5) ∨ True)))) → p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : ((p3 ∧ p5) ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_366598444890551545600676821269 : ((((((((p1 ∨ False) ∨ ((p2 → (p4 ∧ p1)) ∨ (True ∧ p3))) ∧ p2) ∨ (((False ∧ True) → p3) → True)) ∨ (p4 ∨ (p2 ∨ False))) ∧ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118481176304112114382281626532 : ((p3 ∨ ((p4 ∨ (((p1 → (p5 → (((p5 ∨ p1) ∧ (False ∨ (True ∨ p5))) ∧ (p3 → True)))) ∨ True) → p3)) ∨ (True ∨ True))) ∨ (p1 → p3)) := by
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
theorem thm_5_vars_63367117019759125599760028617 : ((p5 ∧ (p4 ∧ ((((p5 → (p2 ∨ False)) → p5) ∧ (False → ((p3 ∧ (((p3 → (p5 → p3)) ∧ p2) ∧ p2)) → (True ∧ p1)))) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683692740457731105535018365347 : (((((p4 ∧ ((p2 → ((p3 ∨ ((p1 → p3) → p5)) ∨ p3)) ∨ ((p4 ∧ p4) → p4))) ∧ p2) ∨ ((p2 → True) ∨ ((p3 ∨ p3) ∨ p5))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174164245285612485176244055959 : (((((p4 ∧ p3) → False) → (False → (True ∨ ((p5 → p2) → True)))) ∨ (p1 ∨ p1)) → (p3 → ((((p5 ∨ (p2 → p1)) ∨ False) ∧ p2) ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727352119347656641458126579940 : ((((p2 ∧ (p3 ∧ p1)) ∨ (p1 → (((p5 ∧ (p4 → ((((p1 ∧ p5) ∧ (p1 ∨ p3)) ∧ (p1 ∧ p3)) → (False ∧ p1)))) → p2) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90939599327715205136252580324 : (((True → p3) ∧ (p5 ∧ (((p5 ∨ True) ∧ ((p2 ∨ (True ∨ ((p3 → p4) ∧ (False → ((p1 → p3) → (True ∧ p3)))))) → p3)) → p1))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248365503535360547385605190313 : ((p2 ∨ p3) ∨ (p5 ∨ (((p3 → (p5 ∨ (((((p3 ∨ p2) ∨ p1) ∨ (p5 ∧ False)) → p5) ∨ (p3 → (p1 → p2))))) → (p5 ∨ p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52095968948898856920143644507 : (((((((p5 ∧ p4) ∨ p2) ∨ True) ∨ (((p4 → False) → True) ∨ (p3 ∧ p1))) ∨ p2) → (p1 ∨ (((p2 ∧ (True ∧ p4)) ∧ p1) ∨ True))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h5 =>
          -- Conjunctions on the left can always be decomposed.
          let h6 := h5.left
          let h7 := h5.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157263457193256450297989707856 : (((((p4 ∧ True) → (p4 ∨ p2)) → ((True ∧ p4) ∧ (p1 ∨ ((p1 ∨ (p4 ∧ p2)) → False)))) → p1) ∨ (False → (((True ∧ p3) → p3) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77992717758521674550191978604 : (((p4 ∨ (((p3 → (((p3 ∨ (((p1 ∨ (p2 ∧ p4)) ∨ p3) ∨ False)) ∨ p2) ∨ False)) ∧ (p1 ∨ (p5 ∨ p2))) ∨ (False → True))) → p4) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ (((p3 → (((p3 ∨ (((p1 ∨ (p2 ∧ p4)) ∨ p3) ∨ False)) ∨ p2) ∨ False)) ∧ (p1 ∨ (p5 ∨ p2))) ∨ (False → True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346384911280820250061320448778 : (p3 → ((p4 ∨ ((p2 ∨ p1) → (p2 → ((True → p1) ∧ ((p5 → ((p2 → (p2 ∧ (p4 ∧ p1))) → p4)) ∨ (p2 ∨ False)))))) ∨ (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4207033287035951790015556612 : (p5 ∨ ((((((p4 ∧ ((p3 ∨ True) ∧ p2)) → p2) → (False ∨ p2)) ∧ False) ∨ (False → ((((p2 → p1) → p2) ∨ p2) → p4))) ∨ p2)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731094071811251985175834246885 : ((((p1 ∨ (True → p5)) → (p1 ∨ (((True ∨ (p5 ∧ p2)) ∧ p5) ∧ ((((((p4 ∨ p5) → p1) → (p3 ∨ False)) → p2) ∨ True) ∨ p4)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46703126062702297918181154458 : (((p4 ∨ (((p2 → (((False ∧ (((p3 ∧ True) ∧ p2) ∧ p5)) ∧ p2) ∧ p1)) ∨ (True → (p5 → (p5 ∨ p5)))) → p3)) ∧ (p5 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81058572329202942222552914122 : (((((False → (p4 ∧ (False ∧ p4))) ∧ p4) ∧ (p3 → (p3 → (((p4 ∧ (p3 ∨ p3)) → (p2 ∨ p4)) ∧ False)))) ∧ ((p4 ∨ p2) ∨ p3)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317055042769257623406253716736 : (p3 ∨ (p4 → ((((((p2 ∨ p2) ∨ ((True → p3) ∨ p2)) → p2) ∧ p5) ∧ (p1 → p2)) ∨ (((p1 ∨ ((p4 ∧ True) ∧ p1)) ∧ p2) ∨ p4)))) := by
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
theorem thm_5_vars_112677597747870006951228256316 : (((((p4 ∧ ((p1 ∧ p4) ∨ False)) ∧ ((p2 ∨ ((p1 ∨ (p1 → (p5 ∨ p3))) ∨ p3)) ∧ True)) → (p4 ∧ (p1 ∨ p2))) → p3) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57699796326102769408619659925 : ((((p1 ∧ False) → p3) → ((((((p1 → p3) ∧ ((False ∧ p1) ∨ p4)) → (p1 → (True ∨ False))) → True) → p2) ∧ (True → (p2 ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327850321050314610360299752516 : (True → ((((p1 ∧ (p5 ∧ (p2 ∧ (p5 ∧ True)))) → p4) → ((((p2 ∧ (((p1 ∧ p3) ∧ p4) ∨ True)) ∨ False) ∨ True) ∨ p5)) ∨ (p1 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



