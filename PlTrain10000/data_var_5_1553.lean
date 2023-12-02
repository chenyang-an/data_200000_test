variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305224670360169542700437486429 : (p1 ∨ (((((p5 ∨ True) → (False ∧ p1)) → p1) ∧ ((p2 → (p1 ∨ (p3 ∨ ((p2 ∨ p5) ∨ True)))) → p1)) → (p4 → ((p1 ∨ p1) ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p2 → (p1 ∨ (p3 ∨ ((p2 ∨ p5) ∨ True)))) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216653060399775420730929052421 : ((((p1 ∨ p5) ∨ p3) ∧ p3) → ((((False ∧ ((p5 ∧ p1) ∧ True)) ∧ (p2 → (False → (p4 ∨ True)))) ∧ (p3 ∧ True)) ∨ ((p2 ∨ p3) ∨ p1))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_860179427769256875506433242077 : ((((((True ∨ p5) → ((((p2 ∧ True) ∨ p3) ∧ True) ∨ (p1 ∧ (p3 ∧ (p3 ∨ ((p1 ∨ p5) ∨ (p2 ∧ p4))))))) ∨ (p5 → p5)) → False) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True ∨ p5) → ((((p2 ∧ True) ∨ p3) ∧ True) ∨ (p1 ∧ (p3 ∧ (p3 ∨ ((p1 ∨ p5) ∨ (p2 ∧ p4))))))) ∨ (p5 → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248258433003347094633944525632 : ((p2 ∨ p2) ∨ (((p1 ∧ ((p4 ∨ ((True ∧ (True ∨ (False → p3))) ∨ ((p5 ∨ p4) ∨ p2))) ∧ p3)) → (False ∨ ((True ∧ p1) ∧ True))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h2
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h2
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h2
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h2
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h2
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45138917788968702698321174146 : ((((p3 → p5) → ((((p1 → (p3 ∧ p5)) ∧ p2) ∨ ((True ∧ (p1 ∨ p2)) ∨ (p3 ∨ (p2 ∨ p4)))) ∨ (p2 ∨ (p3 ∨ p1)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42124670549080681623803919350 : ((((False ∨ p2) → ((((False ∨ p5) ∨ (False ∧ (((p2 ∨ p5) → False) → False))) ∧ ((p3 ∨ (p4 ∧ (p3 ∨ p5))) ∧ p1)) ∧ p3)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136780587318732926590022560677 : (((True → p4) ∧ ((((p4 → p2) ∨ p1) ∨ p3) → (((p5 ∨ ((p4 ∨ (p1 ∧ (p3 → p1))) ∧ p1)) → True) → p2))) ∨ ((False ∧ p3) → p5)) := by
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
theorem thm_5_vars_307140985016526297666814812193 : (p1 ∨ (False ∨ ((((p2 ∧ (p5 ∨ (p1 → p5))) → (True ∧ False)) → (p3 ∧ (True → p4))) ∨ ((False → True) ∨ ((p1 → (p3 ∧ p5)) ∨ p4))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773156962510164196769671549536 : (((False ∨ ((((p1 ∧ ((p4 ∧ (((p1 ∧ ((((True ∧ True) ∨ False) → p1) ∨ (True → p4))) ∨ p1) ∨ p1)) → True)) ∧ False) ∨ False) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254636529176103587111746304024 : ((p3 ∧ p2) → (((p1 ∧ p5) → ((((p2 ∧ (p1 ∨ True)) ∧ (p1 → p3)) → (((True → p3) ∨ p2) ∧ ((p1 ∨ p5) ∨ p5))) → False)) ∨ True)) := by
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
theorem thm_5_vars_233434781306176659606735937040 : ((False ∨ (True → False)) → ((p5 ∨ True) ∧ (((p4 ∨ (False ∧ p1)) ∧ ((((p4 ∨ p3) → False) → False) ∨ (p1 → p4))) ∨ ((p2 ∧ p2) ∨ False)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134032517379023173762878857019 : (((((p5 → (((p1 → p1) ∧ ((((p1 ∧ p1) ∧ False) ∨ (True ∧ p4)) ∨ p1)) ∨ True)) → (p5 ∧ p5)) ∨ False) ∨ p2) ∨ ((p1 ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310300603701195037153892009446 : (p2 ∨ ((((p4 ∧ True) ∨ (p1 ∨ p1)) ∧ ((p5 → p2) ∧ p3)) ∨ ((p2 ∨ p4) ∨ ((p4 ∨ (True ∨ p5)) ∨ (False → (p2 → (p2 ∧ True))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337853148528926731784064406369 : (p1 → (((False ∧ (((True ∧ (False ∧ p2)) ∨ ((p1 ∨ True) → p3)) ∨ p4)) ∨ False) ∨ (True ∨ ((p5 ∧ ((p4 ∨ True) ∨ p1)) ∨ (p3 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249897336881015592654072959016 : ((True → p1) ∨ (((((((p5 ∧ (False ∧ p3)) ∧ p2) ∧ False) ∨ (p1 ∨ True)) ∨ (False ∧ (p1 ∨ ((p5 → p5) ∨ p1)))) ∧ (p3 ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300957480929838722213351792526 : (False ∨ (((((False ∧ p5) ∧ p5) ∨ (p2 → ((p4 ∧ p1) ∧ p5))) ∨ p1) ∨ ((((p2 ∨ (True ∨ (p1 → p3))) ∨ False) → p2) → (True ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118249300269054339181489778960 : ((p1 ∨ (((((((p5 ∧ False) ∧ p4) ∨ True) → (p5 → p4)) ∨ p5) → (((p5 → p4) → p1) ∧ p5)) ∧ (p5 → (p4 → False)))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218009900368003834513824754390 : (((True ∨ p1) ∧ (p5 → p5)) → ((((p5 ∧ (p2 ∧ p5)) ∨ (True ∨ True)) ∨ ((p2 ∨ p2) ∨ (False ∧ (((p5 ∨ p2) ∨ p2) ∧ p2)))) ∨ p1)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257933755449214010077812834706 : ((p4 ∨ False) → (((((p2 → (((p5 ∧ p4) → p1) ∧ False)) ∧ (True → p1)) ∧ p3) ∨ (p4 → p2)) → ((((p3 ∨ p1) ∨ p5) ∧ p1) ∨ p2))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h10 := h7 h9
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h14 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h15 := h12 h14
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319164548655748612834580224795 : (p4 ∨ (((((p3 ∨ (((p2 → (p5 ∨ False)) → p1) ∧ (p2 ∧ True))) → p1) ∧ p4) ∧ (p5 ∨ p2)) ∨ (((p5 → p1) → (p5 ∨ p1)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64075244220976399623416923600 : ((False ∨ (((((((((p1 ∧ p3) → p3) ∧ p2) ∨ True) ∧ p3) ∨ p1) → p2) ∨ p1) ∧ (((p3 ∨ p3) ∧ ((p5 → p1) ∨ p1)) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739272838158657489559710098912 : ((((p4 ∧ p2) ∨ ((p1 → p5) ∧ ((p2 ∧ ((p3 ∨ (p1 ∧ p2)) → (p4 → True))) ∧ (p4 ∨ (((p3 ∧ p1) ∨ (p4 ∧ False)) ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303835118286771582570533586008 : (p1 ∨ ((((p3 ∧ (p2 → ((p1 ∨ p5) → ((((p3 → ((p3 ∧ p4) ∧ p3)) ∧ False) ∧ True) ∧ (p2 ∧ p1))))) ∨ True) ∨ (False ∧ p4)) ∨ False)) := by
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
theorem thm_5_vars_213624354161745954477217040174 : ((((p3 ∧ p2) ∨ p4) ∨ p1) ∨ (((True ∧ p5) ∨ (p5 ∨ True)) ∨ (p5 ∧ (p1 → (p5 ∧ ((True ∨ ((p3 → (p1 ∨ p5)) ∨ p3)) ∧ True)))))) := by
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
theorem thm_5_vars_42312638929549687815119576394 : (((p2 ∧ (((p1 → p2) → True) ∧ ((((p5 → (p5 ∨ (p4 ∧ p3))) ∧ p1) → ((p3 ∨ p2) ∧ ((p1 ∧ True) ∨ p2))) ∧ p2))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354825947220362206255130641443 : (p5 → ((((p2 ∨ p5) ∧ True) → (((False → True) ∨ ((True ∨ ((p3 ∨ (p3 ∨ (p4 → p3))) → (p2 → (p3 → False)))) ∨ p4)) → p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312373941171594192762791547838 : (p2 ∨ (p3 → (((True ∧ ((p2 ∨ p1) → p2)) ∧ ((p3 → p3) → p4)) ∨ (p2 ∨ (((True → p2) ∧ p3) → (p1 → (p2 ∧ (p2 ∧ True)))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h2.left
  let h9 := h2.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h11 := h8 h10
  -- One of the premise coincides with the conclusion.
  exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320989615809653056896186356527 : (p4 ∨ (False ∨ (((((p2 ∧ (False ∨ p2)) → True) ∨ ((p3 → ((p5 ∨ (p4 ∨ p5)) → p3)) ∨ (True ∨ p2))) → (p2 ∧ (True ∧ p5))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218548695040625431457616869697 : (((True → p1) → (p3 ∧ False)) → (((True → (p2 ∧ False)) ∨ ((False ∨ (True → True)) → (p5 ∨ p5))) → ((p3 → (p4 ∨ p1)) ∨ (p3 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713274175644193498889892994418 : ((((p4 ∨ (((p4 ∧ p2) → p3) → p1)) ∨ ((False ∧ ((True → (p3 ∧ (True → p3))) ∨ (((False ∨ p5) ∨ True) → (False → p3)))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116407960220194511338822854808 : (((True ∨ (p2 → p2)) → (((True → (((p1 → p3) ∧ ((p5 ∨ p2) → p3)) → p5)) ∧ p3) ∨ ((True ∧ p1) ∧ (p5 ∧ True)))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4204957508348023327126952131 : (p5 ∨ (((((((p5 ∧ (p1 → True)) → (((True ∨ p1) → False) ∨ (p1 ∧ False))) ∧ (p1 → (p1 ∨ p1))) ∨ p3) ∨ False) ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308486620566747189837546419470 : (p2 ∨ (((((((p4 → p5) ∧ p1) → ((p5 ∧ p2) ∧ False)) → (((p4 ∧ p3) ∧ p1) ∨ p2)) ∨ (p4 ∧ p2)) ∨ ((False → p1) ∨ p4)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39756766831042454283717276958 : (((True → ((p4 ∨ (p2 → ((((((p3 ∧ p5) → p2) → p1) ∨ (p5 → (p4 ∨ True))) ∨ p2) ∨ (p4 ∨ (p1 ∨ False))))) → p4)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337657221999600091755287518227 : (p1 → (((((((p4 → p1) ∧ p3) ∨ p1) ∨ p1) → (False ∨ ((p1 ∨ True) ∨ p5))) ∧ (p2 → p4)) ∨ ((p5 → p2) ∨ (False → (False → p4))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134345145417935928552991494901 : (((p5 ∧ (((p1 → (((p5 ∧ (p4 ∨ p5)) ∨ True) ∧ False)) ∧ p2) ∧ ((p2 ∨ p5) ∨ (p2 ∧ (p4 ∧ p2))))) ∨ False) ∨ (p2 → (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_523982408353644318627224417434 : (((True ∧ ((p5 → ((False ∨ (p2 ∧ (True ∨ ((((True ∨ (False ∨ p1)) ∨ True) ∧ (p4 → False)) ∨ p2)))) ∧ False)) → (p3 ∨ (p5 → p3)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249022579302745131373411989851 : ((p4 ∨ False) ∨ ((False → p3) → ((((((True ∨ p3) → (p1 ∨ False)) ∧ (False → p4)) ∨ ((True ∧ (p4 → p2)) → p5)) ∨ (True ∨ p2)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748993228565611326698574331956 : ((((p4 → p4) → (((False ∨ p4) ∧ False) ∨ (p2 ∨ ((False ∨ ((((False ∧ p5) ∨ (p5 ∧ False)) ∧ (p2 ∨ (p4 ∨ p2))) → True)) ∨ p3)))) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9041166851503128880023093132 : (((((((True → (False ∨ (True ∨ ((p2 → p2) ∨ p5)))) ∨ p2) → False) ∧ p3) ∨ (((p1 ∨ (p1 ∧ False)) → (p3 → False)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136380453699023226008100374699 : ((((p1 → p3) ∧ (p5 ∧ p5)) ∨ (p2 ∨ (p4 ∨ (((p1 ∨ (p4 → ((True ∧ (p1 ∧ p5)) ∨ p5))) ∨ p4) → p4)))) ∨ (True ∨ (p2 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75792975044237995019453191660 : (((((((p3 ∨ False) → False) ∨ p4) ∨ (((False ∧ (p5 ∨ ((((p5 → (True ∧ p5)) ∨ False) → True) ∧ False))) ∨ p4) ∧ p4)) ∨ True) → False) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p3 ∨ False) → False) ∨ p4) ∨ (((False ∧ (p5 ∨ ((((p5 → (True ∧ p5)) ∨ False) → True) ∧ False))) ∨ p4) ∧ p4)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214785566779944507601881007283 : (((False ∨ p5) ∨ (p1 ∧ p1)) ∨ ((p5 ∧ p4) ∨ ((p1 ∧ (((p3 ∨ p1) → False) ∧ ((p3 → ((True → p3) ∨ (p4 → True))) → p2))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337821840069570386842425508439 : (p1 → (((((p2 → p2) → ((p3 → p3) → ((p2 ∨ p3) ∨ p3))) → p3) ∨ True) ∧ (p5 ∨ (((p5 ∨ (p1 ∧ p3)) → p2) ∨ (p3 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678173647762616174974603685068 : ((((((True ∨ False) → (p3 ∨ ((((False ∨ p2) → True) → p4) ∨ False))) → ((p4 → (p1 ∧ True)) ∨ p2)) ∨ ((True ∧ p5) ∨ (p3 ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68089122917208166246500378395 : ((p2 → (p5 ∨ ((p4 ∨ ((p5 ∧ ((True ∨ ((p3 → p4) → ((False → False) ∨ p1))) ∧ p4)) ∨ (p1 ∧ False))) ∨ ((p2 ∨ p5) ∨ False)))) ∨ p1) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173774830860307194575553580481 : ((((False ∨ p2) ∧ ((p5 → ((p4 ∧ p4) → p5)) ∨ ((p5 ∧ p1) ∨ p5))) ∨ p4) → (p1 ∨ (p2 ∨ ((p3 ∨ p4) ∨ ((True ∨ False) ∨ p4))))) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h6
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112848450203234407521325499726 : ((((p1 ∧ (False → p2)) ∧ ((False ∧ (False ∧ (((((p5 ∧ p3) ∨ False) ∧ (p1 ∧ False)) ∧ True) ∧ p1))) ∨ (p5 ∨ p5))) → p3) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68349578306390806829324704394 : ((p3 → ((False ∧ ((p5 ∧ (p2 ∧ (p4 → (False ∧ True)))) ∧ p5)) ∨ ((False ∨ (True → ((p5 ∧ p1) → (True ∧ p1)))) ∨ (p4 → p3)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257266845138436137574460588010 : ((p2 ∨ p3) → (((True → True) → (p5 ∧ (((True ∨ p2) → ((p2 ∧ p2) ∧ True)) → p5))) ∨ (False → ((p5 → (False → True)) ∧ (p5 ∧ p4))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179055827343096036023867120063 : (((p5 → False) → (p5 ∨ (((p2 ∧ p1) ∧ False) ∨ (False ∨ (False ∨ p1))))) ∨ ((((p2 ∧ p1) → (p1 ∨ (True ∨ p2))) ∨ (p4 → True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671577197956948310281960329596 : ((((p5 → (((((p2 ∧ (False ∧ (p1 → True))) ∧ (False ∨ p1)) ∧ p3) ∧ ((p5 ∧ (p1 ∧ p4)) ∧ True)) ∨ p5)) ∨ ((p3 → p1) ∨ p5)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_65614623623237449843807650821 : ((p4 ∨ ((p1 ∨ (((p2 ∧ ((p4 ∧ p5) ∨ p5)) ∨ p5) ∧ ((((p5 → p2) ∧ (True ∨ p5)) → (p4 ∧ (True ∧ p1))) ∧ p3))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46801008232387144359633392698 : ((((((p3 ∧ ((((p4 ∧ (p3 → p4)) ∨ ((p3 ∨ p1) ∨ False)) ∧ ((False ∨ p4) ∧ p3)) → p5)) ∨ p1) ∧ p4) ∧ p3) ∨ (p3 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260090208670992359325607463962 : ((p2 → False) → (p2 → (p2 → ((p5 ∨ ((((p1 ∧ p4) → (p1 ∨ p3)) ∨ ((True ∧ p2) ∧ p2)) → p4)) ∧ (p4 ∧ ((True ∧ p2) ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158494787094215365228187035354 : (((p3 ∧ p3) → (((True → True) → p2) ∧ (((p5 ∧ ((p4 ∨ p5) ∧ p5)) → (p5 ∨ p3)) → p4))) ∨ ((((p2 ∨ p5) → True) ∧ False) → False)) := by
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
theorem thm_5_vars_56625931281095205150706282803 : ((((p2 ∧ p5) ∧ p2) ∧ ((p1 ∨ (((p4 → p3) → (p5 → p5)) ∧ (p5 ∧ ((True ∧ (p4 ∧ p3)) → p4)))) ∧ (p2 ∧ (p2 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166444465731056405009571288943 : ((p2 ∨ ((p2 → (p3 ∨ (p4 ∨ (p4 → ((p3 ∧ (p1 ∧ p5)) ∧ (False ∧ False)))))) ∨ p5)) ∨ (((((p1 → p3) ∧ False) ∨ True) → p2) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 → p3) ∧ False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50601285418555124243032601681 : (((((((p1 ∨ p3) ∨ p3) → (p2 → (False ∨ ((p5 ∨ True) ∨ p5)))) ∨ (p4 → p2)) ∨ (p5 ∨ p4)) → ((p3 ∧ p2) ∨ (True ∨ True))) ∨ p2) := by
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
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115044867016145077808154974879 : ((((p4 ∧ ((p5 ∧ (True → p5)) ∧ ((p5 ∨ p1) ∧ p4))) ∨ False) ∨ (p4 → ((p3 ∨ (True → p4)) ∨ (True ∧ (p2 ∧ p5))))) ∨ (p5 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47341204275993967237345565850 : ((((p3 ∨ False) ∧ (False ∧ (p1 ∨ (((((p3 ∧ (p3 ∧ (((p2 → p1) ∧ p4) ∧ p3))) → False) ∧ p5) ∧ p1) ∧ p4)))) ∨ (p4 → True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315158068082791834922007954858 : (p3 ∨ ((((p2 → p2) ∧ True) ∨ (p4 ∨ False)) → ((((False ∧ p2) ∨ ((p4 ∨ (p1 ∧ p5)) → (p5 ∨ (p3 ∨ p5)))) → p1) ∨ (False → p1)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
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
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42677895949001040303013170229 : (((p4 ∨ (p4 ∨ (((p2 → p5) ∨ (p2 ∧ (False → ((p2 → p3) ∧ (((((p1 ∨ False) ∧ True) → p4) ∨ p2) ∧ p4))))) ∨ False))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657940185924064418270239440537 : ((((p1 ∧ (p1 ∧ (((True ∨ ((False ∨ (p2 ∧ True)) ∨ p1)) ∧ (p5 ∧ (True ∨ p1))) ∧ ((p1 ∧ p1) ∨ (p4 → True))))) ∨ (p2 → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228702346578334385918077861598 : ((p2 ∨ (p4 ∨ p3)) ∨ ((True ∨ (p2 → ((((False ∨ (p4 → p4)) ∨ p1) → p4) → (p3 ∨ (p5 ∧ p5))))) → (p4 ∨ (False ∨ (True ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665412654333360967467660351671 : (((((True → ((((p3 ∨ p4) ∨ (False ∨ p1)) ∨ p1) ∨ ((p5 → ((p1 ∧ p4) → True)) ∨ (True ∨ False)))) ∧ p3) ∧ (p5 → (p2 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734077906771581253861397860974 : ((((True ∨ p3) ∧ ((p4 ∨ p4) ∨ ((p2 ∨ ((p3 ∧ (((p3 ∧ ((p2 → p5) ∧ p1)) → p3) ∧ p4)) → (p5 ∧ (p3 ∨ p4)))) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314931400029907016942465350736 : (p3 ∨ ((True ∧ (p3 ∨ ((p4 ∨ p2) ∨ ((False → False) → p1)))) ∨ (False ∨ ((((p5 ∧ (p3 ∨ p3)) ∧ ((p1 → p5) → True)) ∧ True) → p5)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232648724254464347560579534602 : ((p1 ∧ (True ∧ p2)) → ((((p1 ∧ ((p2 ∧ p4) ∨ (((True → p3) ∧ p1) ∨ (p2 ∨ p4)))) ∧ ((p4 ∨ p4) ∧ p1)) → (p1 → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109767801448189580067670018937 : ((p5 ∨ ((((p1 ∨ (p3 → (p1 ∨ (p4 ∨ p1)))) ∧ p3) ∨ (((p4 → p4) ∨ p5) ∧ ((p2 ∧ False) → (False → False)))) ∨ p2)) ∧ (True ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774757218161606229131522242666 : (((False ∨ (((False → (p5 ∨ p3)) ∧ (p3 ∨ p3)) ∧ ((((p3 ∧ (p5 → p4)) ∨ p5) ∨ (p2 → (((p4 ∨ True) ∧ p3) → True))) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64677076145334242694037811038 : ((p1 ∨ (p3 ∨ ((((p3 ∨ p2) ∧ True) → (p2 → (p5 → (((p1 ∨ p2) ∧ ((p3 ∧ p4) ∨ True)) ∧ p1)))) → ((p3 → p4) ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149244077910293559693045872092 : (((False ∨ p5) ∨ ((p1 ∨ ((p5 ∧ ((p5 → False) → True)) ∨ ((True ∨ (p5 → p5)) ∧ (p3 ∧ p2)))) ∨ True)) ∨ (True ∨ (p1 ∨ (p5 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617247053711674046534639373839 : (((((p5 ∧ (((p3 ∧ p5) ∨ True) ∧ (p1 ∨ p2))) ∨ (p5 ∧ (True → ((p3 ∧ True) ∨ ((p4 ∧ p5) → ((False ∨ False) → p3)))))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_712648024449778936543425110836 : (((((p3 ∧ p3) ∧ ((False ∨ p1) ∨ p5)) ∨ (p4 → (False → (((False ∨ True) ∨ (True → False)) ∨ (((p4 → p2) → (p3 ∨ True)) ∨ False))))) ∨ p2) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320468722383015575676132101994 : (p4 ∨ ((p1 → False) → ((((p2 ∧ ((p5 → p3) ∧ True)) ∧ True) ∨ (((((p4 ∧ True) → p2) ∧ False) → p5) → ((p5 → p4) ∨ True))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115099867473688665078481724499 : ((((((False ∧ p5) ∧ p4) ∨ ((False ∧ (p5 → p2)) → p5)) ∧ p4) → (p3 ∨ (((p4 → p5) → (p3 → (p5 ∨ p2))) → p1))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49108257244523778441097149584 : (((((False ∨ (p1 ∨ (p3 → (p1 → p3)))) ∨ ((p2 ∨ p1) ∧ (p5 ∧ True))) ∧ ((True ∨ p5) ∧ (p2 → False))) ∨ ((p1 → p5) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174300300612293363795738692002 : ((((False → ((p5 ∧ (False ∨ p1)) → (p5 ∨ p2))) ∨ p3) ∨ ((p2 ∧ p4) ∨ False)) → (((True ∧ (p2 ∨ (p1 ∧ p2))) → (False ∨ p2)) ∨ p5)) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h23
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h26
      case inr h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h29
    case inr h30 =>
      -- False on the left can always be used.
      apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61142024067275495097426883231 : ((False ∧ (((False ∨ p5) → ((p4 ∨ True) ∧ False)) ∨ (((True ∧ p5) ∨ (((p4 ∧ (((p1 ∨ p4) ∧ p5) → p3)) → p1) ∧ p5)) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263567253348831290813544129922 : (True ∧ (((((True ∨ p2) → True) ∨ ((p5 ∧ ((p3 ∧ p4) ∨ True)) → False)) → ((p4 → (p5 ∨ p4)) → False)) ∨ (p2 ∨ ((True → True) ∨ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44967650709773082734120581351 : ((((True → p1) ∧ ((((p4 → p5) ∧ p5) ∧ (((((False → p3) ∨ p2) → ((True → (p4 → p1)) → p4)) → p5) → p4)) ∧ p4)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184511247160504670312592615773 : (((False ∧ (p2 ∨ ((p3 ∨ (p4 → False)) ∧ True))) ∨ (p2 → p5)) ∨ (((p5 ∨ p5) ∧ p3) → (p5 → ((True ∨ False) ∧ ((p1 ∨ True) ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
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
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h13 =>
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h14 =>
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230036651319221582187696934618 : (((p1 ∧ p3) ∧ p5) → ((((p2 → p1) ∧ (p5 ∨ (True ∨ (p2 → False)))) ∧ (p4 ∨ (p2 ∧ p2))) → (((p2 ∧ (p2 ∧ True)) ∧ p5) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h1.left
      let h10 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h1.left
      let h17 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h16.left
      let h19 := h16.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h1.left
        let h24 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h25 := h23.left
        let h26 := h23.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- Conjunctions on the left can always be decomposed.
        let h30 := h1.left
        let h31 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h32 := h30.left
        let h33 := h30.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h34 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h35 =>
        -- Conjunctions on the left can always be decomposed.
        let h36 := h1.left
        let h37 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h38 := h36.left
        let h39 := h36.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h40 =>
        -- Conjunctions on the left can always be decomposed.
        let h41 := h40.left
        let h42 := h40.right
        -- Conjunctions on the left can always be decomposed.
        let h43 := h1.left
        let h44 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h45 := h43.left
        let h46 := h43.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741164537592561126866022182653 : ((((p4 ∨ p1) ∨ (True ∧ (((p5 ∨ (((True → (True → (p4 ∨ (p5 ∧ (((p4 ∧ False) ∧ p1) ∧ p2))))) → p4) → p2)) ∧ p4) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698218997527944666916291603902 : ((((((p1 ∨ True) ∨ ((False ∧ ((False ∧ True) ∧ p1)) → p2)) → p1) ∨ (True ∨ ((False ∧ p3) ∧ ((p1 → (p4 ∨ (p3 → False))) ∧ p4)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_44441582019592839670826529782 : ((((False → (((p5 → False) ∧ ((p4 ∧ p5) → p3)) → (p5 ∨ p2))) ∧ (p3 ∧ ((p3 ∧ True) ∧ ((p5 → p4) ∨ (p4 → p4))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157591840957646240582869080407 : (((p1 ∨ (False → (True ∧ ((p3 ∧ (p1 → p5)) ∨ (p5 ∨ (p5 ∧ (p2 ∧ p3))))))) → (p2 ∧ p3)) ∨ (p2 → ((p2 → True) ∨ (p1 → p2)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789888825165420252660440753456 : (((p5 ∨ (((p3 → p4) ∧ p3) → ((False ∧ (p3 ∧ p2)) ∧ ((p1 → (p5 ∨ (p4 → p4))) → ((p2 → ((p4 → True) → p5)) → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310237802563705864928774593501 : (p2 ∨ ((((False → True) ∧ (((p5 → p2) ∧ p3) ∧ True)) ∧ (p3 → False)) → ((p1 ∧ (((p1 ∧ (p5 ∨ True)) ∧ p4) ∨ (p4 ∧ p3))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h8 := h6.left
  let h9 := h6.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h10 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h11 := h3 h10
  -- False on the left can always be used.
  apply False.elim h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h15.left
  let h17 := h15.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h20 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h19
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h21 := h13 h20
  -- False on the left can always be used.
  apply False.elim h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198590400062223979719236560040 : ((p2 ∨ (((True ∨ p5) ∧ (p2 → p5)) ∧ p2)) ∨ (((((p1 ∧ p2) ∧ p1) ∧ (((False → p4) ∧ p5) ∧ True)) ∨ (p4 → p2)) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51554465206402337043983030059 : (((p5 ∧ (((p4 ∧ (((p1 ∧ (p4 → p1)) ∧ p2) ∧ p2)) ∧ ((False ∧ p1) ∨ p3)) → p4)) → (((p1 ∨ p2) ∨ (True ∧ p1)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618948253403139007728818959829 : ((((((False ∨ True) ∧ p2) ∨ ((p4 ∧ p3) ∨ ((p4 ∧ ((((False ∨ p4) ∧ p3) → (p1 → (p1 → (p3 ∨ False)))) ∨ True)) ∨ p3))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49483938376900030633894768658 : ((((((p1 ∧ True) → ((False → (p4 ∧ (p4 ∧ False))) → (p4 ∨ (False → True)))) → ((False ∨ p2) → p3)) → False) → ((True → p3) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39066431250784280674723280798 : ((((p5 ∧ p5) ∨ (p3 ∨ (p2 ∨ ((((True ∨ True) ∧ p2) → p2) ∨ (p3 → (p3 ∧ ((p1 → p5) ∧ ((p1 → p3) ∧ p3)))))))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679994744822010742952721246920 : ((((((False → ((p3 ∧ p2) ∨ p4)) → ((p2 ∧ p2) ∧ ((p4 → p3) ∨ (True → (p3 → p1))))) → p3) → (p3 → (p2 → (p5 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_821273789107296450617471108 : ((p3 ∧ (True → ((((((True → False) ∧ ((False ∨ (p1 → p1)) → p5)) ∧ ((p3 ∧ p4) ∨ p2)) ∧ p1) ∧ (True ∧ p4)) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246082938620286210175203631846 : ((p4 ∧ p1) ∨ ((((p2 ∧ True) ∨ (((p1 ∧ p2) ∨ p5) → ((p2 ∨ True) → (True ∨ (True → (True ∨ (p1 → p5))))))) → p4) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158328350267928388166719146525 : (((True ∧ p2) ∧ ((True ∧ (p3 ∨ (p4 ∧ True))) ∧ ((False → ((False ∧ p1) → (True ∨ p4))) → p5))) ∨ ((p2 → True) ∨ (p2 ∨ (True → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248463377322279660339202422505 : ((p2 ∨ p5) ∨ ((((p2 → False) ∧ (((p5 ∨ p5) → p5) → p1)) ∧ p5) ∨ (p3 → (True ∨ (True → ((True ∨ ((True → True) ∨ p5)) → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



