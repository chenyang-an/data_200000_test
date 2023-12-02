variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49117553519974397335598589064 : ((((((p1 ∧ (p2 ∧ ((p1 → False) ∨ (True ∨ True)))) ∧ (p5 → False)) → True) → (p5 ∧ ((p1 → False) → False))) ∨ (p4 → (True ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173306528458899990314656149918 : ((p1 → (p1 ∧ ((p2 → (((False ∧ p4) ∨ (True ∧ (p1 ∨ p1))) ∨ p5)) → p2))) ∨ (True ∨ ((False → (True ∧ p1)) ∧ ((False ∨ p3) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184099011736413603792179464141 : ((((True ∧ p2) ∧ (p5 ∨ (p1 → ((p3 ∨ p1) → False)))) ∨ p3) ∨ (((True ∨ (p2 ∨ p5)) ∧ False) → (False → (p5 ∨ (p4 ∧ (p1 ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307512490796408082183113318912 : (p1 ∨ (True → (((p1 ∧ p2) ∨ (False ∨ p1)) ∨ ((True ∨ ((((True → p4) ∨ (p3 ∨ (p2 ∨ p5))) ∧ p4) ∧ p2)) ∨ (True ∧ (p3 ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193179859922174937002687890584 : (((((False ∨ False) ∧ p3) → p4) → ((False ∧ True) ∧ True)) → (p2 ∨ (((p4 ∨ p5) ∧ ((True ∧ p2) ∨ (False → p2))) ∧ ((p4 ∧ p4) → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False ∨ False) ∧ p3) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668695411827334031429228465617 : (((((((((p2 ∧ False) ∧ True) ∧ p3) ∧ (p3 → ((p5 ∧ (p1 ∨ p3)) → ((p2 → p2) ∧ p5)))) ∧ p5) ∨ p1) ∨ (p4 ∨ (True ∨ p4))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_807973271326248325968352968243 : (((p4 → ((p2 ∨ p2) → ((((p1 ∧ (False → p3)) ∨ p2) ∧ ((p1 ∧ (p4 → (False ∨ p1))) → (p2 → p3))) → (p4 → (False ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248199569952729462281567903319 : ((p2 ∨ p1) ∨ ((p2 ∧ (((p3 → False) ∨ ((p1 → ((False → p1) ∧ (p2 → p3))) ∨ True)) ∨ (((p2 → (p5 → p5)) ∨ p2) ∧ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342289991316337265482587992195 : (p2 → (((((p1 ∨ p3) ∨ True) ∨ False) → ((p5 ∨ (((p1 → p1) ∧ p3) ∧ False)) ∧ (p4 ∧ p3))) ∨ ((p3 ∨ True) ∨ ((p2 ∧ p3) → p5)))) := by
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
theorem thm_5_vars_163676703981858162939445642985 : (((p1 → False) ∨ (((((p2 ∧ True) ∨ False) → (((False ∨ False) ∨ False) ∧ p1)) → p2) ∨ True)) ∧ (((((p2 ∨ p1) → True) ∨ False) ∧ True) ∨ True)) := by
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
theorem thm_5_vars_328289522616960088076340675856 : (True → (((p4 ∨ ((p4 ∨ (False → ((p4 → p2) → (False ∨ p5)))) ∧ p3)) ∨ (p5 ∨ (p2 → (p3 ∧ False)))) ∨ (p3 → (False → (p1 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353983206725674515429028346653 : (p4 → (p3 → (((False → p3) ∧ ((p4 ∧ p1) ∧ (p1 → p5))) → (((p3 ∨ p1) → (p5 ∧ ((((p1 ∨ p4) ∨ p5) ∨ False) → p2))) ∨ True)))) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665509217500569964737571521795 : ((((((((p3 → ((p2 ∧ ((p3 → (p1 ∨ True)) → True)) ∨ False)) ∨ p1) ∨ ((p4 ∨ p2) → p3)) → p3) ∨ p1) ∧ (p3 → (False ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616774736720004121428835484364 : ((((((p1 ∨ p1) → ((False ∧ True) ∨ (p1 → (False ∨ p5)))) ∨ (True ∧ (p5 ∨ ((((p5 ∨ p3) ∨ (p5 ∨ p3)) → p4) → p3)))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733270665297371498359634485081 : ((((p3 ∧ p4) ∧ ((p3 ∨ ((p4 → p5) → (((p3 ∧ ((p2 ∨ (p3 → p5)) ∨ True)) ∧ False) ∨ (True ∧ (False → (p4 ∨ p1)))))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674710667180667081333896965872 : ((((p2 → ((p5 → p5) ∨ (True → ((False → p1) → ((p4 ∧ (True → (((p4 → p3) ∧ p4) ∨ p3))) → p2))))) → ((True ∨ True) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142862311316991728399124668334 : ((p4 ∨ (((False ∧ (p3 ∨ p4)) ∨ (((p5 ∨ (p4 ∧ p3)) → p2) ∧ (p5 ∨ p4))) ∨ ((p5 ∨ p4) → (p5 → p3)))) → (p5 ∨ (False ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- False on the left can always be used.
        apply False.elim h6
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344115493244115295075310258181 : (p2 → (False ∨ (((((p1 → p1) → (p2 → ((((p1 ∧ p3) ∨ p4) ∧ p2) ∨ (p1 ∨ False)))) ∧ ((p3 → p1) ∧ p2)) ∧ p5) ∨ (False ∨ True)))) := by
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
theorem thm_5_vars_37502643122893711190696520763 : (((((p5 ∨ p1) ∧ ((((((p5 → (p1 ∨ p4)) → p1) ∨ ((True ∨ (p1 → p1)) → True)) ∨ (p5 → p1)) ∨ True) → p4)) ∨ True) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641079067494998400321421848830 : (((((p5 ∧ p3) ∨ (((True → p3) ∧ (((((p4 → True) ∧ p2) → p2) ∨ p1) ∧ (((p2 → (p5 ∨ True)) → p3) → p5))) ∨ p3)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305582422800481414550084042880 : (p1 ∨ (((((p2 → (False ∨ True)) ∧ ((True → p2) ∨ p1)) ∨ p2) → False) ∨ (True ∨ (((((p2 ∨ (p1 ∨ True)) → False) ∨ p5) → p2) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89301395744276414585286854675 : (((False ∨ (p2 → True)) ∧ (((((False ∧ (p1 ∨ p5)) ∨ (p4 → p5)) ∨ (False → (p2 ∧ p5))) ∧ ((True ∧ (p5 ∨ False)) → p5)) → False)) → p3) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : ((((False ∧ (p1 ∨ p5)) ∨ (p4 → p5)) ∨ (False → (p2 ∧ p5))) ∧ ((True ∧ (p5 ∨ False)) → p5)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h7
      -- False on the left can always be used.
      apply False.elim h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h6
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75784994798633881595450659312 : ((((((p5 ∨ ((p1 → p5) ∧ p1)) ∨ p2) ∨ ((False → False) ∧ ((p2 ∨ ((False → False) ∧ (p5 → p1))) ∨ (False ∨ True)))) ∨ False) → p2) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p5 ∨ ((p1 → p5) ∧ p1)) ∨ p2) ∨ ((False → False) ∧ ((p2 ∨ ((False → False) ∧ (p5 → p1))) ∨ (False ∨ True)))) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52716716769796933783212237053 : ((((((((p1 ∧ (p4 ∨ p2)) ∨ p3) → p4) → p1) ∨ (p4 ∨ p2)) ∧ p3) → ((((((False ∧ p4) ∨ p1) ∨ True) ∨ False) → p2) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62035159667781864922388060338 : ((p2 ∧ ((p3 ∨ False) ∧ (((((False ∧ True) ∧ True) ∨ p3) → p4) → (((p1 ∧ (p3 ∨ ((p5 → (True ∨ False)) ∧ p3))) ∧ p4) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346359392840114027538596456015 : (p3 → (((p3 ∧ p4) ∨ ((False ∨ p3) ∧ (((p1 ∨ (((p3 ∧ (p3 ∧ False)) ∧ p4) ∧ ((p3 → p2) ∧ True))) → p1) → False))) ∨ (p3 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54478337490537850855165145967 : ((((((True → p2) ∧ p5) → False) ∨ (True ∧ p3)) ∨ (((((p1 → p1) ∧ (p1 ∧ (((p2 ∨ p4) ∧ True) ∧ True))) → p1) ∧ False) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135641145784252364217848941057 : (((((((p4 ∨ p5) → True) ∧ ((p1 ∨ (p1 ∧ p5)) → p2)) ∧ p1) ∨ (p5 → p2)) → ((p3 ∨ p1) ∧ (False ∧ False))) ∨ (True ∨ (p4 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_132846566253144435584733070304 : ((p2 ∨ (p3 → (((p5 → True) ∧ p1) → (((p2 ∨ p3) ∧ (True ∧ p5)) → (p5 ∧ ((p3 ∨ p5) → (p4 ∨ p3))))))) ∧ ((p3 ∨ False) → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h2.left
    let h10 := h2.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h5.left
    let h13 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h2.left
    let h15 := h2.right
    -- One of the premise coincides with the conclusion.
    exact h13
  -- Implications on the right can always be decomposed.
  intro h16
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h3.left
    let h19 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h2.left
      let h24 := h2.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h19.left
      let h27 := h19.right
      -- Conjunctions on the left can always be decomposed.
      let h28 := h2.left
      let h29 := h2.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h30 =>
    -- Conjunctions on the left can always be decomposed.
    let h31 := h3.left
    let h32 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h31
    case inl h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h32.left
      let h35 := h32.right
      -- Conjunctions on the left can always be decomposed.
      let h36 := h2.left
      let h37 := h2.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h38 =>
      -- Conjunctions on the left can always be decomposed.
      let h39 := h32.left
      let h40 := h32.right
      -- Conjunctions on the left can always be decomposed.
      let h41 := h2.left
      let h42 := h2.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  -- Implications on the right can always be decomposed.
  intro h43
  -- Disjunctions on the left can always be decomposed.
  cases h43
  case inl h44 =>
    -- One of the premise coincides with the conclusion.
    exact h44
  case inr h45 =>
    -- False on the left can always be used.
    apply False.elim h45



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725986763892756767680280932455 : (((((p4 → p2) ∧ p4) ∨ (((((p5 → ((p2 ∧ p3) ∨ p2)) ∧ p2) → p4) ∨ (True ∨ (p3 → (False → True)))) ∨ ((p5 → p1) ∨ True))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714074150364452883292374646965 : ((((((p1 ∨ True) ∧ (p3 ∧ False)) → p2) → (((True → p5) → p1) ∧ (False → (((p4 → p4) ∧ False) ∧ ((True ∨ p5) ∨ (p1 → p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356470213495673569300721670636 : (p5 → ((((p2 ∨ False) ∨ ((False ∧ p5) ∧ (p2 ∨ p3))) → (False ∧ p4)) → (((p3 ∨ p5) ∨ p3) ∧ (((False ∨ (p4 → p2)) ∧ False) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147245121116578680966619537212 : ((((((p4 ∧ (p5 ∨ p4)) → p2) ∨ (((p1 ∧ (p5 ∨ False)) → (True ∨ p2)) → (p2 ∨ False))) ∧ False) ∨ True) ∨ (((p4 → p5) → False) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264744120674376925026571777906 : (True ∧ ((True → True) ∧ ((((False ∨ ((False → (p5 → p2)) ∧ (p4 → ((p4 ∧ p4) → (p1 ∧ False))))) → p3) ∧ True) ∨ (p3 → (False → p2))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329740908641009980691094130102 : (True → ((p5 → p4) → ((p1 → (p4 ∧ False)) ∨ ((((p3 → (False ∧ (False → (p3 ∧ p3)))) ∨ (p5 ∧ p3)) → p5) → (p2 → (p1 ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322473233512021119230611603023 : (p5 ∨ (((p4 ∧ p3) ∧ (((p4 ∧ (p2 ∧ ((p3 ∧ ((p2 ∧ True) ∧ ((p2 ∨ p2) ∨ False))) ∨ ((False ∧ p3) ∧ p2)))) ∧ p3) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157776843165393104360531429414 : ((((False ∨ ((((p4 ∨ p5) ∨ p4) ∨ (p5 → p3)) ∨ p3)) ∨ p5) ∨ ((p4 ∨ p3) → (p1 ∨ True))) ∨ (True → (((p5 ∧ p2) ∧ True) → p3))) := by
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
theorem thm_5_vars_115351223952358522053242075832 : ((((((p2 ∧ p4) ∨ p4) ∧ (p4 ∨ p3)) ∧ True) ∧ (True ∧ (False → ((True ∧ (p2 ∨ (p4 ∨ (p2 ∨ (False ∨ True))))) ∨ False)))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65555410194516888360907458688 : ((p3 ∨ (p1 → (((p5 ∨ p3) ∧ ((((p5 → (p5 → (p2 ∧ False))) ∨ False) ∨ (p1 → (p1 ∧ True))) → p5)) → ((False ∧ p2) ∨ True)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_47392861388343518418923811585 : ((((p4 → True) → ((((p3 ∧ (((p2 ∧ p1) ∨ (((p3 → p2) ∧ p1) ∧ p5)) ∨ (p4 ∧ p3))) → True) → p4) ∧ False)) ∨ (True ∨ p5)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318569370982087794245957211831 : (p4 ∨ ((((((p1 ∧ p4) → ((p1 ∨ True) ∧ p4)) ∨ True) → ((p3 ∨ (p4 ∨ (p5 → (p5 → p2)))) ∨ (p3 ∨ p1))) → p1) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779069540209849756721235089309 : (((p1 ∨ (p5 → ((p5 ∨ True) → (p5 → (((p4 ∧ (True ∧ (p1 ∧ (((p5 ∧ (p1 ∧ True)) → p2) ∧ p3)))) ∨ p1) ∧ (p4 → p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678667095946634204404280163374 : (((((p3 ∧ p2) ∨ (p2 ∧ ((((True ∧ p5) → (p1 → ((p4 ∨ (p5 ∨ p4)) ∨ p3))) → False) ∧ p4))) ∨ ((p5 ∧ False) → (p2 → p1))) ∨ p5) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37773139317639441719028870684 : (((((p1 → (p5 ∨ p5)) → ((p3 ∧ False) → ((((True ∧ (p4 ∧ p5)) ∨ (p4 → (True ∧ p3))) → (p5 ∨ p3)) → p1))) → False) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315283039812129726112991638605 : (p3 ∨ (((False ∧ (p4 ∧ True)) ∨ p4) → (((((p3 ∧ (p3 ∨ True)) ∧ p2) ∨ ((p5 ∧ p4) ∧ ((p2 ∧ (p2 → p4)) ∨ p3))) ∨ True) ∨ True))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62050449942894466037761059374 : ((p2 ∧ ((p4 → p1) ∨ (((p2 → (False → p1)) ∧ (((p5 → p5) ∨ p1) → p5)) ∨ ((((p3 → p4) ∨ True) ∧ True) ∧ (True ∨ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61605121268127561656169470539 : ((p1 ∧ ((False ∧ p4) ∧ (p4 ∧ (((p1 → (p3 ∨ ((p3 ∨ (p1 ∧ (p5 ∨ True))) ∧ ((p2 → (False → p4)) ∧ p2)))) ∨ p5) ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140156098936098345978910889490 : ((((True → ((p4 ∧ (p4 ∧ (p5 → ((((False ∨ (p1 ∧ p5)) ∨ False) ∨ p5) ∧ p1)))) → p4)) → p3) → (True → p1)) → ((p3 ∧ True) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49713965599623148299978156949 : (((True ∧ (((p2 → (p3 ∧ p3)) → (p3 ∨ (p5 ∧ p3))) ∨ ((p4 → (((p3 ∧ p3) ∨ False) ∨ p5)) ∨ False))) → (p1 ∨ (p3 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136338542328073028340202655367 : (((p3 ∧ ((p4 ∨ True) ∧ p5)) ∧ (((True ∨ (p5 → (p3 → (p5 → (p5 ∧ p3))))) → p1) → (False ∨ (p4 ∧ p4)))) ∨ ((True → p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190684564880329416637652467514 : (((p5 → ((((p3 → p1) → p4) ∧ p5) → True)) → p4) ∨ ((True ∧ ((p3 ∨ ((p3 → p4) → p1)) ∨ ((False → False) ∨ False))) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357426470057327973720849096830 : (p5 → ((p3 ∨ p1) → (p5 → (((p3 → (p2 ∧ p4)) ∨ ((p4 ∧ (p5 ∧ p3)) ∨ (p2 → (p3 → p1)))) → (p2 → ((p1 ∧ p1) ∨ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h8
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h16
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h19 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h19
        -- One of the premise coincides with the conclusion.
        exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324196128983396063560335332346 : (p5 ∨ (((p4 → ((p1 ∨ p4) ∨ ((p2 ∧ False) ∨ False))) → True) → (((False ∧ ((False → True) → False)) ∨ (p4 ∨ False)) ∨ (True ∨ (p1 → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171878459018752326418205597132 : (((p5 ∧ ((True ∨ (((p5 ∨ p4) → (True ∨ p2)) → p3)) ∨ (True → False))) → p2) ∨ ((p2 → ((False ∧ p5) ∨ ((p5 → True) ∨ p5))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695514463647356422251932349754 : (((((((p3 → p5) → (p1 ∨ (True → False))) → p5) ∧ (p1 ∨ (True → p2))) → ((False ∧ (True ∨ p2)) ∧ (p2 → (p2 → (p2 ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193172606878595924707712730159 : (((((True ∨ p2) ∧ p4) ∨ p2) → ((True → p1) ∨ False)) → (p4 ∨ (p2 ∨ (((p3 → p4) ∨ ((False ∧ (p2 → (False ∧ p1))) ∨ p4)) ∨ True)))) := by
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
theorem thm_5_vars_177703428816299870056038200111 : (((((p1 → ((True ∧ p2) ∧ p3)) ∧ (p2 ∧ p4)) → (p5 ∨ False)) ∧ True) ∨ ((True → False) → (False ∨ (p1 ∨ ((True ∨ p2) → (p2 ∨ p5)))))) := by
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
theorem thm_5_vars_192602588832230971777109234777 : ((((((p3 ∧ (p2 ∨ p1)) ∧ p2) ∧ p2) ∧ p2) → p1) → ((((p1 ∨ (False → p2)) → ((((p3 → p5) → p5) ∧ False) ∨ p5)) ∨ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308563326344820530441127250392 : (p2 ∨ ((((False ∨ (p5 ∨ p2)) ∧ (p1 ∧ p5)) ∨ (p3 ∧ ((False → ((False → ((p2 → p3) ∧ (p4 ∧ False))) ∧ (p1 → p3))) → True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148029334130319848401189839608 : (((((p3 → p1) ∧ p3) ∧ ((False ∨ (p2 ∨ (((p2 → p5) ∧ (p5 → p2)) ∧ p5))) ∧ p1)) ∨ (p3 ∨ True)) ∨ (((p2 ∨ False) → False) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159050280277616712090821272061 : ((p5 ∨ ((p2 → (((p5 ∧ (p1 → True)) → (p5 ∨ p4)) ∨ (True ∨ (p3 → (p1 ∧ p3))))) → p2)) ∨ ((p1 ∨ (p4 ∧ p3)) → (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263837542311180231369082745652 : (True ∧ (((False → False) ∧ ((p1 ∨ False) ∨ ((True → p1) ∧ ((False ∨ (p2 ∧ p2)) ∨ False)))) → (False ∨ ((((p3 → p3) ∧ p1) ∧ p1) ∧ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
      -- One of the premise coincides with the conclusion.
      exact h5
      -- One of the premise coincides with the conclusion.
      exact h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h17 := h9 h16
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h18
        -- One of the premise coincides with the conclusion.
        exact h18
        -- One of the premise coincides with the conclusion.
        exact h17
        -- One of the premise coincides with the conclusion.
        exact h17
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h19 =>
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756954837440805054570523962251 : (((p1 ∧ ((((p2 ∨ p2) ∨ True) → (False → p1)) → ((p3 → (p5 ∧ ((True → p2) ∧ p5))) ∨ (((p4 ∧ (p5 → False)) → p3) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152659591156498842706820016765 : (((p2 → False) ∧ (p2 ∧ (True → (((((True ∧ False) ∧ (p4 ∨ p4)) ∨ p1) ∧ p1) → (p3 ∨ (p1 → False)))))) → (p5 ∧ (p1 ∧ (True ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h12 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h13 := h8 h12
  -- False on the left can always be used.
  apply False.elim h13
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h15.left
  let h17 := h15.right
  -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
  have h18 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h16
  -- We have shown the premise of h14, we can now drive its conclusion.
  let h19 := h14 h18
  -- False on the left can always be used.
  apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53715525664494408300734058834 : (((p4 ∨ (((p3 ∨ (p4 ∧ (p5 → p4))) ∧ p4) ∨ p4)) ∧ (((((p5 ∨ (((p4 ∧ p5) → False) ∧ p1)) → True) ∨ p1) → p4) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150669804881465559442202064789 : (((True → (((p1 ∧ (p3 ∧ ((((p5 ∨ p1) ∧ p4) → p3) ∧ p3))) ∨ (True → True)) ∧ (p3 ∧ p5))) ∧ p3) → ((p2 ∧ (p1 ∧ p5)) ∨ p5)) := by
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
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221482865144785995734497554768 : (((p1 → p1) ∨ p4) ∧ ((p5 → ((((p3 ∧ p2) → (False → p3)) ∨ p2) → (p2 ∨ ((p1 ∧ (p1 → (True ∧ (p3 → p4)))) ∨ p2)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40978440054273564714501998508 : (((((p3 → p2) ∨ (((p3 ∨ (((p2 ∨ p5) ∨ p1) ∧ p4)) ∧ ((p1 → (False ∧ p3)) → (p5 ∨ p3))) ∧ p1)) ∨ (p3 ∨ p2)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48661088817161599875774252659 : ((((((True ∨ False) ∧ p5) ∧ (((False ∨ p4) ∧ True) ∧ (False → p1))) ∧ ((p2 ∨ (True → (p3 ∧ p4))) → p2)) ∧ (True ∨ (True ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775002644369069199734177811823 : (((False ∨ ((p5 → (p1 ∧ p4)) ∨ ((p5 → True) → (((p4 ∨ ((p2 ∨ p5) ∨ (True ∨ p3))) ∨ (p5 ∧ (p3 → (p1 → p1)))) ∧ True)))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60107280526868661678855748471 : (((p3 ∨ p2) → ((p4 → p5) → ((((p3 → ((p5 ∨ (p1 ∨ p1)) → p1)) → p4) ∧ ((p4 → p1) ∨ (p2 ∧ (p4 → p1)))) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247829096387671460940005127568 : ((p1 ∨ p2) ∨ (((p3 ∨ p4) ∨ (p5 → (p3 → ((p3 ∧ p3) ∧ ((p1 ∧ p2) → (((False ∨ p3) ∨ ((False ∧ p1) ∧ p1)) ∨ p3)))))) ∧ True)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47603621569053245843424887211 : (((p3 → (p1 → (((p3 ∧ p2) ∨ ((True ∧ p4) ∨ ((p2 ∨ p2) → ((True ∧ (p4 ∧ p2)) → (p2 ∧ p5))))) ∨ p4))) ∨ (p2 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354080360336646016734992683792 : (p4 → (p5 → (((((False ∨ p1) ∧ (p3 ∨ p4)) ∧ (False ∨ p4)) ∧ (p2 → (((((p5 → p4) → p2) → (p1 ∧ p4)) ∨ p4) ∨ p2))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255496400330598668345824264054 : ((p5 ∧ p2) → (((p2 ∧ (p4 ∧ (p2 → ((p1 → (True ∨ False)) → p5)))) ∧ ((p5 ∨ False) ∧ ((p3 → p1) → (p3 ∧ p3)))) ∨ (p1 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327803853430941138545782139197 : (True → ((((((((p2 ∧ p1) ∧ False) → ((p5 ∧ True) → p2)) ∧ p1) → p1) → ((p5 ∧ (True ∨ (False ∧ True))) ∨ p1)) ∨ True) ∨ (p5 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319739990308814325103558907069 : (p4 ∨ (((True ∧ (True ∨ (p3 ∨ p5))) → p4) ∨ ((((p1 → (p3 → ((p1 → (True ∧ p1)) → (p3 ∧ False)))) ∨ (False ∨ p4)) → p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59593918290158565664159047918 : (((p4 → p2) ∨ ((p3 ∧ ((p5 ∨ p2) ∧ ((True ∧ (False ∨ p3)) ∧ (False ∧ (True → (p5 → p3)))))) ∨ ((False → (p2 → p5)) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150074959719028800671125918357 : ((True → ((p1 → (False → p4)) → ((False ∨ p4) ∨ ((False ∧ p1) ∨ ((False ∧ (p2 ∨ (p1 ∧ True))) ∧ p5))))) ∨ (False → (p4 ∧ (False → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260093697074256806186332578784 : ((p2 → p1) → (((p4 → ((p3 → p1) ∧ (((p2 ∧ (p4 ∧ p1)) ∧ (False ∨ ((p5 ∨ p5) ∧ (False ∨ True)))) → (False ∧ p1)))) ∨ True) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646895643014899236317945221972 : ((((p2 → (p5 ∧ ((((False → (p1 → p1)) ∧ (p5 → (p4 → False))) → (True ∨ (p5 ∨ p3))) ∨ (p4 ∧ (p4 ∨ (p5 ∧ p3)))))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58112469991465067060445939719 : (((p1 ∧ p4) ∧ (p3 → (((p5 → True) ∧ ((p5 ∧ p1) → (p2 → p3))) → (((((True → p4) ∧ p1) ∨ (p5 → p4)) ∨ p2) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151920269573048234520912434719 : (((((p5 ∧ ((p3 → (p3 ∧ p3)) ∧ p3)) ∧ (p2 ∧ p4)) ∨ p1) ∧ (((False ∨ p5) → p2) → (p4 → p2))) → ((p1 → (p1 → p3)) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h7.left
    let h13 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h14 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h15 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h16 := h2 h15
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h17 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h18 := h16 h17
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63975537648393196783330328851 : ((False ∨ (((((((p2 → True) ∧ ((False ∨ ((True → False) → p5)) ∨ True)) ∨ False) ∨ p5) ∨ p1) ∧ ((False ∨ p4) ∧ (p3 ∨ p2))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141132501107993059892530580676 : ((((False → ((p2 ∧ p5) ∧ p3)) ∧ p2) ∧ ((p2 ∧ ((p5 → (((False ∨ (p2 ∧ p2)) ∧ False) ∧ p1)) → p3)) → p5)) → (p2 ∧ (False ∨ True))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112178972815047846464501018001 : (((p4 ∧ ((((p3 ∨ p5) ∨ p5) ∨ p2) ∨ ((p5 ∧ ((False ∨ (((p2 ∨ p5) ∨ p1) ∨ True)) ∨ p4)) ∧ (p2 → p2)))) ∨ p4) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178065677702166665620907739636 : ((((((False ∨ True) ∧ p1) ∧ (False ∨ (p3 → (p3 ∧ True)))) ∨ p2) → p3) ∨ ((p1 → ((False ∨ p3) ∨ True)) ∨ (p4 ∨ (p2 ∧ (p4 ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225032204319456987698560197383 : (((False ∧ p2) ∧ p5) ∨ ((p1 ∧ (p4 ∧ p2)) ∨ (False ∨ ((False → ((p5 → False) ∧ False)) ∨ (((((True → p2) → p3) → p2) → p5) ∧ p3))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749443780085766018292756688342 : (((True ∧ (((p4 → (p3 ∧ ((p3 ∧ p4) → ((p4 → True) ∧ (p2 → (p5 ∧ (p2 ∧ p4))))))) → (p4 ∧ (p5 → (p5 ∧ False)))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350322505021188383325347494325 : (p4 → ((True → ((((p4 → (True → (p2 ∨ p1))) ∨ ((p3 → (p1 ∧ p3)) ∨ ((p5 → True) ∧ False))) → p1) ∨ ((True ∧ True) → p4))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117917390451814889915610416132 : ((p5 ∧ (((((p5 ∧ False) → p2) ∨ p1) ∨ p4) → ((True ∨ (((p1 ∧ False) → (p1 ∧ (p4 ∨ (p5 ∧ p4)))) ∧ False)) ∧ False))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57798664284920583884824256420 : (((p1 ∧ (False → True)) → ((((p3 → p2) ∨ ((p1 ∧ True) → (p4 → False))) ∨ (p1 ∨ (((True ∨ True) ∧ (False → True)) ∧ p1))) ∧ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339496942767980267631352170895 : (p1 → (False ∨ ((((True → p2) → (False → p1)) → ((False ∨ ((p4 → ((False ∨ p5) ∧ p4)) → (True ∧ p4))) ∨ False)) ∨ (p3 ∨ (p2 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42519436293161725828775252663 : (((False ∨ (p2 ∨ (((True ∧ (((False ∨ ((p5 → (p2 → p2)) ∧ True)) ∧ p3) ∧ True)) ∨ (p5 ∨ (p2 ∧ (False ∨ p3)))) → False))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247375503183819703697138767493 : ((False ∨ p1) ∨ (((p3 → (p2 ∧ p1)) → p2) → ((((True → False) ∨ (p2 ∧ (p1 ∨ p5))) ∧ p3) ∨ ((((True ∧ True) ∨ False) ∧ p2) → True)))) := by
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
theorem thm_5_vars_711670630139044431044798606074 : ((((p4 → (False ∧ (p4 ∨ (p3 ∧ p4)))) ∧ (((p3 → (((p1 → ((p3 ∧ p4) → p2)) ∧ p4) ∨ p1)) ∨ p4) ∨ ((p1 → p4) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174230659581716226046250176372 : ((((p4 ∧ True) ∨ ((p1 ∧ p1) ∧ ((p3 ∧ (p1 → p1)) → False))) → (True ∨ p3)) → ((((((p2 → p3) ∧ p1) → p2) → p1) ∨ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_132872493781255678037031727514 : ((p3 ∨ ((p4 ∨ (((p3 ∧ ((p3 ∧ p2) ∨ (p3 → ((p1 ∧ p1) → (True ∨ p1))))) → p4) ∧ p3)) → (p5 ∨ p4))) ∧ ((p3 ∧ p5) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (p3 ∧ ((p3 ∧ p2) ∨ (p3 → ((p1 ∧ p1) → (True ∨ p1))))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799123417003281746220274051944 : (((p1 → (True ∧ (p4 → (p5 ∨ ((((p1 ∧ (((p1 ∧ p2) → (p3 → p2)) ∧ p4)) ∧ p2) ∨ True) → ((False ∧ (p3 → p4)) ∨ p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_871858853146643337395372535233 : ((((p4 ∨ (((False ∨ ((((p5 → (p3 ∨ ((((p2 → False) → p5) ∨ p5) → True))) ∧ False) ∧ False) ∨ True)) ∧ (True ∨ p3)) ∨ p2)) → False) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ (((False ∨ ((((p5 → (p3 ∨ ((((p2 → False) → p5) ∨ p5) → True))) ∧ False) ∧ False) ∨ True)) ∧ (True ∨ p3)) ∨ p2)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



