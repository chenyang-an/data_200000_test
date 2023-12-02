variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720816918356502900455473719209 : (((((p5 ∨ (p5 ∨ p1)) → p1) → ((p3 ∧ ((False ∧ (p5 ∧ p3)) → ((p4 → p4) → (((p5 ∧ (True ∨ p2)) ∧ p2) ∨ p2)))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611815621809174821494200646300 : (((((p2 → ((True ∧ p2) ∨ (((((p5 → p1) ∨ (p4 ∨ p2)) ∨ False) ∧ p2) → (((p1 ∨ (p3 → p3)) ∧ p4) ∨ p4)))) → p5) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_124760337215253702812067446012 : (((True ∧ ((False → p4) → False)) ∧ (p4 ∧ (((p2 ∨ (False ∧ (p5 ∧ p5))) ∨ (p1 ∧ (((p2 ∧ p1) ∧ False) → False))) → p1))) → (p3 → False)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h4.left
  let h8 := h4.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h9 : (False → p4) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h11 := h6 h9
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800499294650357704243055881114 : (((p2 → ((((((p2 → p2) ∧ (p1 ∨ (p3 → True))) → (((p3 ∨ p5) ∧ p4) ∨ False)) → (((p2 ∧ p5) ∧ p5) → p3)) ∨ False) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62332633314814741047468368139 : ((p3 ∧ (((p5 ∧ (((((p5 → (p5 ∧ p4)) ∨ False) ∨ (((True → p2) → p4) → p3)) ∧ p3) ∧ p3)) ∨ True) ∧ (p1 → (p3 → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321136782983912679187561967036 : (p4 ∨ (p2 ∨ (((True ∧ ((p1 → p4) ∧ p5)) ∧ p5) ∨ (((False → p1) ∧ p1) → (p2 → (((p3 → ((p1 ∨ p5) ∧ p3)) ∧ p2) ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682693088241781654675088408594 : ((((((p2 → True) ∧ (p5 ∧ (p2 ∧ p4))) → ((p1 ∨ ((p2 ∧ p5) ∨ p1)) ∧ (p2 → p3))) ∧ ((p1 ∧ p3) ∨ ((p2 ∧ p5) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200060897970532736420116622645 : (((p3 → (p2 ∨ (p4 → p3))) → (False ∧ p1)) → (True → (((False ∧ (p3 → True)) ∧ (False ∨ ((((True ∨ True) ∨ p2) → False) ∧ p4))) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p3 → (p2 ∨ (p4 → p3))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h3
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : (p3 → (p2 ∨ (p4 → p3))) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h9
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- False on the left can always be used.
  apply False.elim h13
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h14 : (p3 → (p2 ∨ (p4 → p3))) := by
    -- Implications on the right can always be decomposed.
    intro h15
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- One of the premise coincides with the conclusion.
    exact h15
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h17 := h1 h14
  -- We need to get the left conjuct of h17 based on <expert-advice>.
  let h18 := h17.left
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165920344408690025564866750623 : (((p1 ∧ False) ∧ (p3 ∧ ((True ∨ (p1 ∧ p5)) → (((p3 ∧ (p4 ∧ p5)) ∧ False) ∧ p4)))) ∨ (((p3 → p3) ∧ ((p1 ∧ p4) ∨ p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39946118850864774430189266876 : (((p4 → ((p2 ∨ (False ∧ (((p2 ∧ ((p3 ∧ (p5 ∧ (p1 ∨ True))) → p3)) → p5) → (p4 → (True ∨ (False → p2)))))) ∧ p2)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40748881953049088043223181862 : (((((p1 → (p3 ∨ p1)) → (p4 → (p1 ∨ ((p2 ∨ ((p3 ∨ ((True ∧ p2) ∨ (p4 ∨ (False ∧ p3)))) → p4)) → p3)))) → p1) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88273631976963555983162933245 : (((p5 ∨ (p2 ∨ (p2 → False))) ∧ (True → (((p2 → p3) ∨ ((((True → p4) ∨ True) ∨ p1) ∨ True)) → ((False → p4) ∧ (p4 ∧ False))))) → p5) := by
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
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h8 := h3 h7
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : ((p2 → p3) ∨ ((((True → p4) ∨ True) ∨ p1) ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h10 := h8 h9
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h15 := h3 h14
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h16 : ((p2 → p3) ∨ ((((True → p4) ∨ True) ∨ p1) ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h17 := h15 h16
      -- We need to get the right conjuct of h17 based on <expert-advice>.
      let h18 := h17.right
      -- We need to get the right conjuct of h18 based on <expert-advice>.
      let h19 := h18.right
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191197996367505490143982694544 : ((((p1 ∨ p1) ∨ True) → (p5 → (p3 ∨ (False ∨ p5)))) ∨ ((((p3 ∨ (p1 → (False ∨ ((p5 ∧ p2) ∨ (p4 ∨ p3))))) ∨ p3) ∧ False) ∧ p1)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200327487545540697607877871862 : (((False ∨ p3) ∧ (((p1 ∨ p1) → p4) → p3)) → (((((False → False) → (p2 ∨ p5)) → p5) ∨ False) ∨ (False → (True → (True ∨ (p1 ∧ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58164118801970024588798659431 : (((p3 ∧ False) ∧ (((True ∧ (p2 → p2)) → ((((((p4 ∨ p5) → p3) ∨ p3) ∧ p3) → (p4 ∧ True)) → (p4 ∧ (p5 ∧ p4)))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116470486664499696558092181038 : (((False ∧ p5) ∧ ((True ∧ p4) ∨ (((p3 ∧ False) ∧ ((False ∧ p4) ∧ p1)) ∨ (True → (p3 ∧ (((p2 ∧ p5) ∧ p3) ∨ True)))))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264104521276855549980860073797 : (True ∧ (((p3 ∧ True) ∧ ((True → p2) ∧ ((False ∨ p3) ∨ p2))) → (True → (False ∨ ((p4 ∨ False) ∨ ((((True ∨ True) ∨ p4) ∨ p4) ∨ p4)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h4.left
  let h8 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342560901886112804546524020910 : (p2 → ((((False ∨ ((p3 ∧ False) ∧ ((False → True) → p4))) ∨ p3) ∧ False) ∨ (p4 → ((False → (p4 ∨ p4)) ∧ ((p2 ∨ False) ∨ (p4 ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165931122235881602667511469655 : (((p4 ∧ p3) ∧ (((p1 ∨ (p4 ∧ p2)) ∧ (p5 ∧ p5)) ∨ (((p2 ∧ p5) ∧ p2) ∧ p4))) ∨ (p1 → (((True ∧ p5) ∧ (p2 ∧ p1)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788522071891418645119800281170 : (((p5 ∨ ((p2 ∨ (p3 ∨ ((((p3 ∨ p2) ∧ (p5 → True)) ∨ (True ∨ p1)) ∨ (((p5 ∨ p5) ∧ (p3 ∧ (p5 → p3))) ∨ True)))) ∨ False)) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66137706712445971114677781530 : ((p5 ∨ ((((((False ∨ ((p2 ∧ p2) → ((((p3 ∧ p4) ∧ True) ∨ p1) → p1))) ∧ p2) → (p5 ∨ p1)) ∨ False) → p2) ∨ (False → p2))) ∨ p4) := by
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
theorem thm_5_vars_806613299958682070410181989342 : (((p4 → ((True ∧ ((True ∧ (p5 ∨ (p2 ∨ ((((p3 ∨ (p5 ∨ (False ∧ (p1 ∧ p5)))) → p4) ∧ True) ∧ True)))) ∧ (p4 ∧ p5))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710478908083188185283630718577 : (((((True ∨ ((p1 → p3) ∨ False)) → p5) ∧ (True → ((False ∨ False) ∧ (p1 ∧ (((p2 ∧ (p1 → p5)) → p1) → ((p1 ∨ p4) ∨ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305047354985401162046107079963 : (p1 ∨ ((((((p1 ∨ ((p5 ∨ p3) ∧ (p2 ∧ (True → False)))) ∨ (True ∨ p4)) ∨ ((True ∧ True) ∨ False)) ∧ p2) ∨ p3) → (p5 ∨ (False → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
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
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h12 =>
            -- Conjunctions on the left can always be decomposed.
            let h13 := h11.left
            let h14 := h11.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h12
          case inr h15 =>
            -- Conjunctions on the left can always be decomposed.
            let h16 := h11.left
            let h17 := h11.right
            -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
            have h18 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h17, we can now drive its conclusion.
            let h19 := h17 h18
            -- False on the left can always be used.
            apply False.elim h19
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h22
          -- False on the left can always be used.
          apply False.elim h22
        case inr h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h24
          -- False on the left can always be used.
          apply False.elim h24
    case inr h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- Conjunctions on the left can always be decomposed.
        let h27 := h26.left
        let h28 := h26.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h29
        -- False on the left can always be used.
        apply False.elim h29
      case inr h30 =>
        -- False on the left can always be used.
        apply False.elim h30
  case inr h31 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h32
    -- False on the left can always be used.
    apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805788079104477820880038178403 : (((p3 → (p4 → (((((p1 ∨ ((((((p3 ∧ (p2 ∧ (False ∧ False))) → p4) → True) ∧ False) ∧ p1) → p5)) → p2) ∨ p1) ∨ p1) ∨ True))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639910350610101267682589894885 : ((((((p5 → p2) → p1) ∨ (False ∨ (p4 → (True ∧ ((p2 ∨ p2) → (((False ∨ p2) ∧ p2) → ((p4 ∨ (p3 ∧ p4)) ∨ True))))))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134197239411175615836108361467 : ((((((p5 ∨ True) → (p1 → (p5 ∨ (p3 → True)))) → p1) ∨ (((False ∨ (True → p1)) → False) ∨ (False → p5))) ∨ False) ∨ (p4 → (False ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_345654248971146936692961637104 : (p3 → ((p5 ∧ ((((((((((False ∧ p2) ∧ p2) ∨ False) → (p4 ∨ p2)) → p1) ∧ True) ∨ (p5 ∧ True)) ∨ p1) → p1) → (p4 → p2))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48816657417896194743329708799 : (((p4 ∧ ((p2 ∧ (p4 ∧ (((p5 ∨ p1) → ((((p1 ∧ True) ∧ True) ∨ p3) → (p2 → p1))) ∨ False))) ∧ True)) ∧ (True ∧ (p1 ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116130773027540021165603547016 : (((p1 ∧ (p2 → p3)) ∧ (((p1 → ((p3 ∧ (False ∧ p2)) ∨ p2)) ∧ p3) → ((p4 → (p5 → ((p3 ∨ False) ∧ p1))) ∧ p1))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53050536748490786408569496692 : ((((False ∨ p2) ∨ ((p1 ∧ p5) → (((p2 → p4) ∧ p5) → p5))) ∧ ((((p4 ∧ (False ∨ p4)) → p3) ∨ (p5 ∨ (p3 ∨ p5))) ∨ True)) ∨ False) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324474269124532581779030953083 : (p5 ∨ ((((p5 ∧ p5) ∨ p5) ∧ p4) ∨ (True ∨ ((((((p2 → (p5 ∨ False)) ∨ True) ∧ p5) → ((True ∨ p2) → (p4 ∧ True))) ∧ p5) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186402298898008618196156806205 : (((True ∨ ((p3 ∧ ((True ∧ False) ∨ False)) ∧ (p1 → p3))) → p3) → (p3 ∨ (((((p2 ∨ False) → p1) → (p1 ∧ (p1 → True))) ∨ p1) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ ((p3 ∧ ((True ∧ False) ∨ False)) ∧ (p1 → p3))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62412697193175995819344416708 : ((p3 ∧ (((True ∨ ((p1 ∨ p4) ∨ p3)) → p1) ∧ (((p3 → (p3 ∨ True)) → ((((True ∨ (p2 ∧ p1)) ∧ p3) → p4) ∨ False)) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782274141209948975378796306098 : (((p3 ∨ ((p4 ∧ ((p4 → (((((p4 ∧ p1) → False) → (False ∧ (((p4 ∨ False) ∨ p4) ∧ p1))) ∨ p2) ∧ (p4 → p1))) ∨ p5)) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351119232963971929898632263681 : (p4 → ((False ∨ ((p1 → ((p1 → (((p5 → (p3 ∧ p5)) ∨ p4) ∧ (p2 ∨ (p1 ∨ p3)))) → p1)) ∧ ((p1 ∧ p2) → p1))) → (p3 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_794291184717883244662142943 : ((True ∧ (((p3 ∨ ((((((True → (False → p2)) ∧ p5) ∨ False) → (p2 → p1)) ∨ p1) → (p3 → (p2 → p4)))) ∨ True) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354750139731381327947429274802 : (p5 → (((((p2 ∨ p1) → p5) ∧ ((p3 ∧ p3) ∧ (p3 → ((True ∧ p5) ∨ (p3 ∨ p1))))) → (p4 → (p2 ∧ ((p2 → False) ∧ p2)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118632078676704776970433570567 : ((p4 ∨ ((p4 ∨ (True ∧ p4)) ∧ ((((p3 → p3) ∨ p4) → (p2 ∧ ((False ∧ p1) → ((p5 ∨ (p2 ∨ p5)) ∨ p1)))) ∨ p1))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33807574490384596154265051809 : ((p5 ∨ ((False ∨ ((((((p1 ∧ p2) → False) ∨ (False ∧ p1)) → ((p3 ∨ p3) ∧ (p1 → True))) ∧ p4) ∨ True)) ∨ (p1 ∨ (p3 ∨ p1)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157954874678825717699696998270 : ((((((p5 ∨ (p5 ∧ False)) → p4) ∨ p3) ∨ p5) ∨ ((p4 → (False ∨ (p4 ∧ False))) ∨ (p5 → p5))) ∨ (True ∧ (p2 ∧ (True ∨ (p5 ∧ True))))) := by
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
theorem thm_5_vars_201222751496741036012224277773 : ((p2 → ((False ∧ (p4 → p2)) → (True ∨ p5))) → (((p3 → ((True → (p4 → p1)) ∧ p5)) ∧ (True ∨ ((False → p2) ∨ p5))) ∨ (False → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346766442114620733279935861413 : (p3 → ((((p1 → ((p5 → (((p3 ∨ p5) ∧ True) ∧ (((False ∧ p2) → p4) → p2))) ∧ False)) ∨ p5) ∨ p5) ∨ (p1 ∨ (True → (p4 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19672464788589673075065057777 : (((p4 ∨ ((p2 → ((True ∧ False) ∨ (p2 ∨ (p3 ∨ (p4 ∨ (p2 ∨ p5)))))) ∧ p2)) ∨ (((p1 ∨ p5) ∨ (p2 → p2)) ∨ (False ∧ p3))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773382371983137531178197428690 : (((False ∨ ((True → (p1 ∨ ((p1 ∧ p1) → (((p5 ∨ p4) → (((p3 ∨ (False ∨ p3)) ∧ ((p4 → p4) → p3)) ∨ p2)) ∨ True)))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158447975800223420312961295809 : (((p4 ∨ p3) ∨ (True ∧ (((False ∨ p5) ∨ p4) ∨ ((p4 ∧ (p4 ∨ ((True ∨ p5) ∨ p2))) ∨ True)))) ∨ (True ∨ (p1 ∧ ((p1 ∧ p1) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225397932518845082748964339568 : (((p2 ∨ p4) ∧ p5) ∨ (p5 ∨ ((p5 ∨ ((p5 ∧ p1) → ((p2 ∨ (p2 ∨ p2)) ∨ True))) ∧ (p1 ∨ (True → ((p2 → p5) ∨ (True ∨ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_50340484374256220063712248814 : ((((p4 → ((False ∨ True) → (True ∧ False))) ∧ ((p2 → ((p4 ∨ (p3 ∨ (p1 ∧ False))) ∨ p5)) ∧ p2)) ∨ (p4 ∨ ((True ∨ True) ∨ p2))) ∨ False) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133934681927881735319095182562 : (((True → (p3 ∨ ((p1 ∧ (p4 ∧ (p1 ∨ p2))) ∧ (p4 ∨ ((p5 ∧ ((p4 ∧ p1) ∧ True)) → (p1 ∧ True)))))) ∧ p1) ∨ (p4 → (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55590305415550229421906009389 : (((p3 ∨ (p5 → (p3 ∨ (p4 ∧ p5)))) → (((p4 ∧ ((p1 ∨ True) → (p2 ∧ True))) ∨ p1) ∨ (True ∨ ((False ∨ (p4 → False)) ∨ p4)))) ∨ p5) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192792381128076280195564302355 : (((p2 ∨ (p1 ∧ (p1 → ((p1 ∧ p1) ∧ p4)))) → p3) → (True ∧ ((((p3 → p5) → (p4 ∨ p4)) → ((p1 → p3) ∨ True)) ∧ (p1 ∨ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698712366401027962885577920433 : (((((p4 ∨ p1) ∧ (((p4 ∨ (p3 ∧ (p5 → p3))) → True) → p5)) ∨ ((p4 ∨ (p3 ∨ (p5 ∧ (((p3 ∨ p3) ∧ p5) → p3)))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160602201935137298406602091726 : ((((p4 → p5) ∧ ((p1 ∨ ((False → p5) ∧ p5)) ∧ True)) ∧ (((p3 ∧ (p1 ∧ p2)) ∧ p4) ∧ p4)) → (((p4 ∧ (p4 → False)) ∧ p3) ∨ p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h3.left
    let h21 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h22.left
    let h25 := h22.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311164973370196901488965833918 : (p2 ∨ ((p4 ∧ p5) → ((False ∨ (((((True → p3) ∧ True) ∧ p3) → (False ∨ (p5 → p1))) ∨ ((p3 ∧ False) → p4))) ∧ ((p5 ∨ p5) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h1.left
    let h13 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777280343604628972823848226079 : (((p1 ∨ (((p5 → True) ∨ (((p5 → p5) ∨ ((p4 → ((p1 ∧ p5) ∨ True)) → ((p1 ∧ p3) ∨ p1))) → True)) → ((p2 → False) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215926858732206490851206942366 : ((p3 ∨ (p1 ∨ (p5 → p3))) ∨ (p4 ∨ ((False ∨ p5) ∨ (p4 → (((p2 → p4) ∨ p2) → ((((p2 ∨ False) ∧ p2) ∨ (p1 ∧ p2)) → p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      cases h2
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196176064764258884206191089940 : ((False ∨ (((p1 ∨ False) ∧ False) → (True ∨ p2))) ∧ ((((True ∧ p3) ∨ ((p5 → (p4 ∨ p2)) ∨ (p4 → p2))) ∨ p2) ∨ ((p4 ∨ p1) → True))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206184209088328897477474664735 : ((p5 ∧ (p1 ∨ ((p4 ∨ p2) ∨ p5))) ∨ ((p1 → (p3 → (((((True ∨ ((p4 ∧ False) → (True ∨ p4))) ∧ False) ∨ p2) → p1) ∨ True))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164859486790977959965031814084 : (((p1 ∨ (p2 ∨ ((p5 ∨ ((p3 ∨ (p5 ∧ p3)) ∨ (p1 → (p2 ∨ p1)))) ∨ p5))) ∨ True) ∨ ((p3 ∨ ((p5 ∨ p1) ∧ p3)) → (p2 → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670103633786000644284386969077 : (((((p3 ∧ (p2 ∧ (False ∨ (p1 → True)))) ∧ (((p2 ∨ False) → (p2 ∨ (p1 ∨ (p5 ∨ (p1 → False))))) ∧ p4)) ∨ (True → (p4 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338270567497777548058328567355 : (p1 → (((p4 ∨ (p3 ∧ (p3 → p1))) → p1) → ((p2 ∧ p2) → ((((p4 → p3) ∨ ((p1 → p4) ∧ True)) ∨ (p1 ∨ False)) ∨ (p2 → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321215167281643635251474020882 : (p4 ∨ (p3 ∨ (p1 ∨ ((p1 ∧ (((False ∧ ((p3 → True) ∧ p5)) → ((True ∧ p3) → True)) → (((p2 ∨ p2) ∧ True) → (p5 ∨ p4)))) ∨ True)))) := by
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
theorem thm_5_vars_225973145651841499510106623652 : (((p3 ∧ p2) ∨ False) ∨ (p2 → (p5 → (p4 → ((p2 → (((True → (p1 ∧ (True ∨ ((p1 ∨ (p2 ∨ p4)) → False)))) → p5) → False)) ∨ p4))))) := by
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806926597413708075326776711608 : (((p4 → ((((((p2 → (False ∨ p1)) → (p5 ∧ p5)) ∨ ((p1 → p1) ∨ p4)) ∨ ((p4 → p3) ∧ p4)) ∨ p5) ∧ (p3 → (p5 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326884622322758584077391883177 : (True → ((((p4 ∨ p5) ∧ ((p3 ∧ ((((p4 → (((True → p1) → (p2 ∨ True)) ∨ p3)) → p1) → True) ∨ (p3 ∨ p3))) ∨ p5)) ∨ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213282522073065263884039458621 : ((((p1 → p2) → p2) ∧ True) ∨ (((False → (p3 → p4)) → p1) ∨ (False → ((p3 ∧ p4) ∧ (((p4 ∧ (p3 ∧ False)) ∨ False) ∨ (True ∨ p3)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47934935169497219719505910518 : ((((p1 → ((p3 ∧ ((False ∨ p1) → False)) → ((True ∧ p1) ∨ ((p5 → p4) ∨ (p1 ∧ p1))))) ∧ ((False ∨ False) → p1)) → (False ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350305508376651733663207358307 : (p4 → ((p3 ∨ ((p2 ∨ ((((p5 ∧ True) ∨ False) → ((True ∧ ((p2 ∧ (p2 → p4)) ∧ p2)) → (True ∨ p3))) → True)) → (p1 ∧ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149707710527461446066956164926 : ((p5 ∧ (p3 ∧ (((((p3 → p3) ∨ True) ∧ p5) → ((((p1 ∧ True) → (True ∧ p4)) → p2) ∧ False)) ∧ p3))) ∨ ((False → (True → p2)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248463656377367887576212461441 : ((p2 ∨ p5) ∨ ((p1 ∧ ((((False → (p4 ∨ p4)) ∨ p3) → True) ∧ p5)) ∨ ((((p2 ∨ p5) → p4) → p3) ∨ (((p4 ∧ False) ∧ p1) → p1)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186343651427287801464904486211 : ((((p1 ∧ (p1 ∨ p2)) ∧ (((p1 → p4) ∨ p4) ∨ True)) → p5) → ((p5 ∨ (((p1 ∨ p4) ∨ p4) ∨ (((True → False) ∨ True) ∨ p3))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_159988087474423588995930426188 : (((((p1 ∨ (p4 ∧ p2)) ∧ ((False → False) ∧ p5)) ∨ (p1 ∧ ((True ∨ True) → (p4 ∧ p3)))) → p5) → ((p4 ∨ p5) ∨ ((p3 ∧ True) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147629125670179867339485563643 : ((((((p1 ∨ ((True → ((False → False) ∧ p2)) ∧ p1)) → (p2 ∨ p5)) ∧ ((True ∨ p4) → p3)) → p4) → p4) ∨ ((p5 → True) ∨ (p4 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166267937703697849730710502198 : ((p3 ∧ (p2 ∧ ((((True → False) ∧ (p2 → (p2 ∧ p1))) → (p2 ∧ False)) → (True → p3)))) ∨ (False → (p1 ∧ (p3 ∨ (p2 ∧ (True ∨ p2)))))) := by
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
theorem thm_5_vars_174482042796032081486389811181 : (((p1 ∧ ((True ∨ (p4 ∨ p4)) ∧ p5)) ∧ (((False ∨ (False → p3)) ∨ True) ∨ p2)) → ((p5 → p3) ∨ (((p5 → (False ∨ p5)) ∨ True) ∧ p5))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h7
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- False on the left can always be used.
            apply False.elim h19
          case inr h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
            -- One of the premise coincides with the conclusion.
            exact h7
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h7
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
        exact h7
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h26 =>
            -- False on the left can always be used.
            apply False.elim h26
          case inr h27 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
            -- One of the premise coincides with the conclusion.
            exact h7
        case inr h28 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h7
      case inr h29 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68494292559929571793119588566 : ((p3 → (p1 ∨ (p1 ∨ ((((p1 ∧ False) ∨ (((p1 ∧ (p4 ∧ True)) ∧ ((p5 ∧ p2) → p4)) ∨ True)) ∧ ((p4 ∨ p4) → p4)) ∨ True)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_50175145191334616493371663269 : (((((((((True ∨ (p4 ∧ (True → p5))) ∨ p4) ∨ p3) → ((True ∧ p2) ∧ p4)) ∨ p2) → p3) ∧ p1) ∨ ((p1 → (p1 ∧ p3)) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645364662778535334344586284324 : ((((p4 ∨ (((p4 ∧ p2) ∨ ((p5 ∨ ((False ∨ (False ∨ (p1 ∧ (True ∧ p4)))) ∨ ((True ∨ p5) → (False → p5)))) → p4)) → p4)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204229652999905315301721140246 : ((((p3 → (True ∨ p5)) → False) ∧ True) ∨ ((True → ((((True → p2) → (((p4 → False) ∧ True) ∨ (p5 → True))) → p3) ∨ True)) ∧ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257327347177016680809582648145 : ((p2 ∨ p4) → (((p5 ∨ ((p2 ∨ p3) ∧ (p3 → (p4 ∨ (False → (False ∧ p5)))))) ∨ True) ∨ (p1 ∧ ((((p2 → p2) ∧ p4) → True) ∧ p1)))) := by
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
theorem thm_5_vars_186052625213896482942002783985 : (((((False → (((p3 → p3) ∨ p5) ∧ p5)) ∨ p3) ∨ p2) ∨ p3) → (p2 → (((((p1 ∨ p1) ∨ ((p3 ∧ p2) → p3)) → p3) ∨ p1) ∨ p2))) := by
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
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45886002596543544983038381534 : (((p3 → (p3 ∧ (p4 ∨ (((p2 ∨ (p5 ∧ ((((p3 ∨ False) → False) ∨ p2) ∨ False))) ∧ (p3 ∧ ((p2 → p3) ∨ p2))) → p5)))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191803800323778186875750043992 : ((p2 ∨ ((False ∧ (p5 ∧ (False ∨ p5))) ∨ (p4 ∧ p2))) ∨ (((False ∧ (p5 → (False → p3))) → (p3 → ((p5 ∧ p4) ∧ p5))) ∨ (False ∧ p2))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37494557906048336329301604896 : ((((((p5 → p2) ∧ p2) → ((p2 ∧ ((p4 ∧ (p5 → False)) → p5)) ∧ (p3 → (p4 → ((p2 → (p4 ∨ p1)) ∧ p3))))) ∨ p5) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14519995901430017344198778898 : (((((((p5 → p4) ∨ p4) ∨ ((((False ∨ p1) ∨ (False ∧ (((p2 ∧ False) ∧ p5) ∧ p2))) → p3) → False)) ∧ p4) ∨ p2) ∨ (False → p1)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68402876717818825464501150053 : ((p3 → ((True ∧ (True → p4)) → ((((p5 ∨ (p3 → p2)) ∨ ((((p5 ∧ p2) ∧ ((p2 ∧ p1) → p3)) ∧ p3) ∨ p4)) → p2) ∨ p3))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113479859968901891155465088374 : (((((p4 ∨ ((True → True) ∧ (((False ∨ True) → p2) ∧ (False ∨ (True → (True ∨ p3)))))) ∨ p1) ∨ (p4 ∧ False)) ∨ (p1 → p1)) ∨ (p3 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118563788089017631103008477242 : ((p4 ∨ ((((((True ∨ (p2 ∨ p3)) ∨ (((((p4 ∧ p4) ∨ p3) ∨ True) → p5) → p4)) → p5) ∨ False) ∨ (p5 → False)) ∧ p3)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671279158432394789084982808053 : ((((p5 ∨ ((((p1 ∧ p1) ∧ (p3 → p1)) → ((p3 ∧ ((p2 ∨ False) → p5)) ∨ (p5 ∨ True))) ∧ (p1 → False))) ∨ ((p2 → p2) → True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_41456675299075357067895218748 : ((((((p2 → p2) → (p5 → p2)) ∧ ((p5 ∧ (p2 ∨ True)) ∧ p5)) ∧ (p3 ∨ (p3 → (((p2 → (p3 ∨ p4)) ∧ False) ∧ p2)))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712622018803990027170243802171 : (((((p2 → (True → p1)) → (p1 → p3)) ∨ (p1 ∧ (p5 ∨ (((p2 ∧ ((p3 → True) ∧ ((p4 ∧ p3) → p2))) ∧ (p4 ∨ True)) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245918334283693234868176281348 : ((p3 ∧ p5) ∨ ((p2 → ((False ∨ p1) → False)) → (((True ∧ ((p4 ∨ p3) → False)) → p5) ∨ ((p3 ∨ ((p3 ∨ (p5 ∧ p2)) ∧ p4)) → True)))) := by
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
theorem thm_5_vars_244932996972632820084869712220 : ((p1 ∧ p3) ∨ (((p5 → (((((True ∨ ((True ∧ p4) ∨ p4)) ∧ p4) → p3) ∧ (p3 ∧ p2)) ∨ p3)) ∧ (p2 ∧ p5)) ∨ (False → (p1 ∧ p3)))) := by
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
theorem thm_5_vars_49394657707635051977344317684 : (((((p2 ∨ (((p2 ∧ p3) ∧ (False ∧ ((p2 ∨ p4) ∧ (p1 → p3)))) → (True ∧ p1))) → (p4 ∨ p2)) ∧ p1) → (p5 ∨ (p5 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52508405650765154337146759883 : (((((((p3 ∨ (p5 ∨ p2)) ∧ False) ∨ p3) ∨ (p3 → (p4 ∧ p3))) ∧ True) ∨ (p1 → (True ∨ ((p4 → (True ∨ False)) ∧ (p2 ∧ p2))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112239645445586118397772380833 : (((p3 ∨ ((p4 ∧ ((p3 → ((((p3 → p1) → (p4 ∨ (False ∧ p4))) ∨ ((True ∨ p3) ∨ p5)) ∧ True)) ∨ p2)) ∧ p1)) ∨ p1) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_889446833382159737453764246678 : ((((((p1 ∨ p1) → p5) ∨ ((True ∨ ((True → p4) → True)) → ((((p1 ∧ p1) → True) → p1) ∨ (p3 → (p1 ∨ True))))) → (False ∧ p4)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ p1) → p5) ∨ ((True ∨ ((True → p4) → True)) → ((((p1 ∧ p1) → True) → p1) ∨ (p3 → (p1 ∨ True))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337392461797287791873209851754 : (p1 → ((p2 ∨ (((((p4 ∧ False) ∧ p5) → ((p5 ∧ p2) ∨ (((p1 → p3) → p2) → True))) → (False ∧ False)) ∧ p3)) ∨ ((False ∨ True) ∨ False))) := by
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
theorem thm_5_vars_806244290439941449476523539186 : (((p4 → ((((p5 ∨ p5) → (p4 → (p4 ∧ ((True ∧ (((p4 ∨ p1) ∨ p2) → (p2 → p1))) ∨ p3)))) ∨ ((p3 → p2) ∨ False)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231630282207702425688246207693 : (((False ∧ False) → p1) → (((((p4 ∧ ((((p2 ∨ (p3 → p3)) → p4) ∨ (p2 ∧ p1)) ∧ p5)) ∨ p5) ∨ (p5 ∨ p3)) ∧ p4) ∨ (p3 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



