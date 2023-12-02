variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_24353860353529957178614267547 : ((((True ∨ False) ∨ p2) ∧ (p5 ∨ (p5 ∨ (((((((p4 → (p1 ∧ False)) ∧ False) → False) → (p4 ∨ p3)) → p1) → p1) ∨ (False → False))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_319268773877881579136528256470 : (p4 ∨ (((((p4 → (p1 ∨ (p5 ∧ p5))) ∨ p5) ∨ ((p4 → (True → False)) ∧ p3)) → False) ∨ (((p5 → (p4 ∨ p1)) → (p3 ∧ p5)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670098580327254381702696444917 : ((((((p4 ∧ p2) ∨ (p5 → (p1 ∧ p5))) ∧ (((p4 ∨ p3) → ((p1 ∧ (p2 ∨ False)) → (False ∨ p5))) → p4)) ∨ (p3 ∨ (True ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173226188307391075372288856374 : ((True → ((((True ∨ p1) ∧ False) ∨ ((False ∨ (p5 ∨ p2)) ∧ (p3 → p4))) ∧ p3)) ∨ (((p5 → p5) ∨ (p4 ∨ (True ∧ p5))) ∨ (p5 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165091425475921111687233644924 : (((p3 ∨ ((((False ∨ (True ∨ (True → (p5 → p3)))) ∨ p1) ∧ True) ∨ (p3 → p4))) → p5) ∨ (False ∨ (((False ∨ p2) → (p1 ∨ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351047834470712043931078844196 : (p4 → ((((p5 → (((False ∧ (p3 ∨ ((False ∧ p4) ∧ p2))) ∨ True) ∨ (False ∨ p2))) ∨ (p2 ∧ (True → (p1 ∧ p2)))) → False) → (p5 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p5 → (((False ∧ (p3 ∨ ((False ∧ p4) ∧ p2))) ∨ True) ∨ (False ∨ p2))) ∨ (p2 ∧ (True → (p1 ∧ p2)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156988503369556568969562180987 : (((((p5 → (p2 → False)) → (p1 ∧ False)) ∨ (p3 → ((p4 → (p4 ∧ (p5 → p4))) ∧ p3))) ∨ p1) ∨ (((p3 ∨ True) ∧ p3) ∨ (p5 ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_92324083820657170701554256186 : (((True ∨ p5) → (((p1 ∨ (p2 ∧ ((False → (True ∧ ((p3 → True) ∧ (True → (p3 → (p5 ∧ p1)))))) ∧ (p2 ∨ p5)))) ∨ p2) ∧ False)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227480611105271931208455465462 : ((True ∧ (p4 ∧ p1)) ∨ ((p3 → (((p4 ∧ p5) → p4) → True)) ∧ (((p3 ∧ p1) ∨ True) ∧ ((p5 → (False ∨ (p5 → False))) ∨ (p2 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116308612879595157346828106901 : (((p2 → (p4 → p3)) ∨ ((True → p2) → (p1 ∨ (((p5 ∨ (p1 ∧ (True → p1))) → ((p1 ∨ p2) ∨ (p2 ∧ p4))) ∨ True)))) ∨ (p5 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_172004219224156080861701251435 : ((((False → (((p1 → p4) ∧ False) ∧ ((False ∧ False) → p1))) → p2) ∨ (False → p4)) ∨ ((p3 → ((p2 → p3) → (False ∨ p3))) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327188849848311700420286407509 : (True → ((p3 ∨ (((((((p1 ∧ ((p1 ∨ True) ∨ p3)) ∧ p3) → (False → (True ∧ ((False ∧ p1) ∨ False)))) → p4) ∧ p2) ∨ False) ∨ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231412116599765601129494750368 : (((p1 → p3) ∨ p2) → (True ∧ (((((True ∧ (((False → True) → ((False ∨ p2) ∨ p3)) ∨ ((p2 → p1) → False))) ∧ p4) ∨ p2) ∨ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_738415335894401492200342832748 : ((((p1 ∧ p1) ∨ (p3 ∨ (p3 ∧ ((p4 → ((p5 → ((((p4 → True) ∧ p5) ∨ True) ∧ ((True ∨ p2) → p3))) ∨ True)) ∨ (True → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113560631714234414298348378572 : ((((p5 → p5) ∧ ((((p5 ∧ p4) ∨ (p1 ∧ ((((p4 ∨ p2) → p2) ∧ p5) ∨ (p5 → p3)))) ∨ p2) ∨ p4)) ∨ (True ∨ p5)) ∨ (p4 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78034852084937757553658281332 : (((p5 ∨ ((p1 ∨ (p3 ∧ (((p4 → (p4 ∧ (True → ((p3 → p3) ∨ (True ∧ False))))) → p1) ∨ p2))) ∨ ((p4 ∧ p1) → p1))) → p3) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ ((p1 ∨ (p3 ∧ (((p4 → (p4 ∧ (True → ((p3 → p3) ∨ (True ∧ False))))) → p1) ∨ p2))) ∨ ((p4 ∧ p1) → p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632690667821010230032278843606 : (((((p4 → (((p5 ∨ True) ∨ (((p4 → p5) ∨ p5) ∧ ((((p4 ∨ p5) ∧ True) ∨ p3) → p4))) → ((False → p3) ∨ True))) → p5) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355557785734398758010389333154 : (p5 → (((p4 ∨ (((p4 ∨ True) ∨ ((p4 → p2) ∨ (p2 ∨ p5))) ∨ ((True ∧ p5) ∨ ((True → True) ∧ (p2 → True))))) → False) ∨ (True ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94725978493148520184941191549 : ((p3 ∧ (((p2 → (((True ∧ (p4 → p5)) ∨ (p2 → (p3 ∨ (p1 ∨ True)))) ∨ p1)) → p1) ∧ ((((p4 ∧ p5) → p3) ∧ p1) → p5))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p2 → (((True ∧ (p4 → p5)) ∨ (p2 → (p3 ∨ (p1 ∨ True)))) ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136628476563807012715252263073 : ((((p2 ∧ p5) ∨ p4) → ((False ∧ (p3 ∨ ((False → False) ∧ p1))) ∨ (p3 ∨ ((p1 ∧ (p4 ∧ (p5 → p1))) → p4)))) ∨ ((True ∧ p2) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305278547505763908494320278362 : (p1 ∨ ((p1 ∨ (((p1 ∨ (p3 → ((False ∨ p1) ∨ p3))) → ((p2 → False) ∧ True)) ∨ (p3 ∨ True))) ∧ ((p3 ∧ p2) ∨ (p3 → (p4 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53707192827359572695178587993 : (((p1 ∨ ((p3 ∧ (p3 ∨ True)) ∨ ((True ∨ False) ∨ p2))) ∧ (False ∨ (p1 → (((p4 ∨ (False ∨ p3)) ∧ (p2 ∨ p5)) ∨ (True ∨ p1))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_160593742096510977225405027755 : ((((p4 → (((p4 ∨ p5) → (False ∨ p2)) → p2)) → p3) ∧ (False ∨ ((p2 → (p3 ∧ p4)) → p5))) → ((p3 → p4) ∨ (False → (p2 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160940191588666791240422930792 : ((((True ∧ p1) ∧ p3) ∧ (((((p3 ∨ (True ∨ p3)) ∧ ((p4 ∧ p1) ∧ True)) ∨ p5) ∨ p2) ∨ False)) → (((p4 ∧ p5) ∨ False) → (False ∨ p1))) := by
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
    let h6 := h1.left
    let h7 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h17 =>
            -- Conjunctions on the left can always be decomposed.
            let h18 := h16.left
            let h19 := h16.right
            -- Conjunctions on the left can always be decomposed.
            let h20 := h18.left
            let h21 := h18.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h21
          case inr h22 =>
            -- Disjunctions on the left can always be decomposed.
            cases h22
            case inl h23 =>
              -- Conjunctions on the left can always be decomposed.
              let h24 := h16.left
              let h25 := h16.right
              -- Conjunctions on the left can always be decomposed.
              let h26 := h24.left
              let h27 := h24.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h27
            case inr h28 =>
              -- Conjunctions on the left can always be decomposed.
              let h29 := h16.left
              let h30 := h16.right
              -- Conjunctions on the left can always be decomposed.
              let h31 := h29.left
              let h32 := h29.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h32
        case inr h33 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h11
      case inr h34 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h35 =>
      -- False on the left can always be used.
      apply False.elim h35
  case inr h36 =>
    -- False on the left can always be used.
    apply False.elim h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168205484843072552840220281834 : ((((p5 ∨ p4) → p5) ∨ (((True ∧ p3) ∨ p3) ∧ ((p1 → (False ∨ (True ∨ True))) ∨ True))) → (p5 ∨ (((p3 ∨ p3) → p3) → (p3 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- Implications on the right can always be decomposed.
        intro h13
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- Implications on the right can always be decomposed.
        intro h16
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- Implications on the right can always be decomposed.
        intro h20
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h22
        -- Implications on the right can always be decomposed.
        intro h23
        -- One of the premise coincides with the conclusion.
        exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748185023705135727782708635558 : ((((p1 → p5) → ((p1 ∨ ((False ∨ True) ∧ ((p3 → p5) ∨ ((((p3 ∧ p2) → (True ∨ p3)) ∧ p1) ∨ ((p4 ∧ False) ∧ True))))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172733549667899536412543177667 : (((p3 → p1) ∨ (((p2 ∧ p2) → (True → p2)) → ((p3 ∨ False) → (p5 ∨ p5)))) ∨ (p5 → ((p2 ∨ p2) → ((p5 ∨ (p3 → p4)) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681507633574293506143609543734 : ((((True → ((p2 ∨ ((((p2 → p2) ∨ (p1 ∨ True)) ∨ p2) ∧ (p3 ∧ (p2 → (p3 ∨ True))))) ∧ p2)) → (p5 ∨ (p2 ∨ (p1 ∨ p2)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58086773445570880382412459342 : (((p1 ∧ False) ∧ ((((((False ∧ p4) → p4) → False) ∧ False) → (False → (((p4 ∨ (p2 ∨ False)) ∨ p3) → p2))) → ((False ∨ p5) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345642612879344392623496241397 : (p3 → ((p3 ∧ ((p4 ∨ (((p2 → (True ∧ True)) ∨ (((False ∧ p4) ∧ ((p4 → (False ∧ p2)) → p5)) ∧ (False ∨ p5))) ∧ p4)) → p2)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336446736610760895307875308881 : (p1 → ((p5 ∨ ((((True → (((p5 ∨ (p2 ∧ (p5 → False))) ∨ (False ∧ False)) ∨ False)) → (((p3 ∧ p1) → p3) ∨ True)) ∨ p1) → p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594365090722338991897693574667 : (((((((True ∨ p3) → p5) ∨ ((((((False → p5) ∨ p2) ∧ p1) ∧ p4) → p2) ∧ False)) ∧ (((p3 ∧ p2) ∧ p3) ∨ (p3 ∧ p2))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669571779156474072508124805156 : (((((((p5 ∧ (p1 ∧ True)) ∨ (p1 ∨ (p1 ∧ (p4 ∨ p4)))) ∧ (p2 ∧ (p2 → p3))) ∧ (True ∧ (p4 ∨ p4))) ∨ (True ∨ (True ∧ p3))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_234109803409909107175818287517 : ((True → (False ∨ False)) → (p3 → ((((True → False) ∨ (((True ∧ (p2 → (p5 ∧ p2))) ∧ p5) ∨ p1)) ∧ p2) → (True → ((False ∧ False) ∧ True))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h17 := h1 h16
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- False on the left can always be used.
        apply False.elim h19
    case inr h20 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h21 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h22 := h1 h21
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- False on the left can always be used.
        apply False.elim h23
      case inr h24 =>
        -- False on the left can always be used.
        apply False.elim h24
  -- Conjunctions on the left can always be decomposed.
  let h25 := h3.left
  let h26 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h25
  case inl h27 =>
    -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
    have h28 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h27, we can now drive its conclusion.
    let h29 := h27 h28
    -- False on the left can always be used.
    apply False.elim h29
  case inr h30 =>
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- Conjunctions on the left can always be decomposed.
      let h34 := h32.left
      let h35 := h32.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h36 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h37 := h1 h36
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h38 =>
        -- False on the left can always be used.
        apply False.elim h38
      case inr h39 =>
        -- False on the left can always be used.
        apply False.elim h39
    case inr h40 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h41 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h42 := h1 h41
      -- Disjunctions on the left can always be decomposed.
      cases h42
      case inl h43 =>
        -- False on the left can always be used.
        apply False.elim h43
      case inr h44 =>
        -- False on the left can always be used.
        apply False.elim h44
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158504204999526007081580116815 : (((True ∨ False) → (p2 ∨ ((p5 ∧ ((True → ((p5 ∨ p4) ∧ p1)) ∨ (p3 → p2))) ∨ (p2 → p2)))) ∨ ((p4 ∨ p3) ∨ (True ∧ (p2 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724911504392060889538294129414 : ((((p5 ∨ (p4 ∨ True)) ∧ ((p2 ∨ ((p4 ∧ p1) ∨ False)) → ((((p4 ∨ (p4 ∨ True)) ∧ False) → p2) ∧ (False ∨ (p1 → (p5 ∨ p1)))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190765992132105870662308307469 : ((((((p2 → p1) → True) → False) ∧ False) ∨ (True ∧ p3)) ∨ ((p5 ∨ (p5 ∨ p2)) ∨ ((True ∨ p3) → (p4 → (False → (p1 ∨ (p3 ∧ False))))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703896338343751776051156080410 : ((((((False ∨ p3) → (((p3 ∧ p1) → True) ∨ p4)) ∨ p3) → (((((False ∨ (p2 ∧ (True ∨ p3))) ∨ p5) → (p3 ∧ False)) ∨ p3) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14912968471097977474043565030 : ((((((p4 → False) ∧ True) ∧ False) ∨ ((((p1 ∨ False) ∨ (((p4 → p5) ∧ p5) ∧ p5)) ∧ ((p4 ∨ p2) → p2)) ∧ p1)) ∨ (p5 → True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684479686977629629429832644092 : ((((((p2 ∨ (True ∧ p3)) ∨ (p1 ∨ p4)) ∧ ((p1 → p3) → (((True ∨ p2) → p3) → p5))) ∨ (True → (p2 → ((True ∧ p5) → p5)))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64014567341920143822280995812 : ((False ∨ (((True ∧ ((p3 ∨ p3) ∨ ((True ∧ (p5 ∨ (p2 ∨ False))) ∨ (p3 ∨ p2)))) ∧ ((p1 → p5) → (False → True))) ∨ (True ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766567058757443551055737113881 : (((p4 ∧ (p4 ∧ (((((p5 → p4) ∨ (True ∧ True)) ∨ (p3 ∨ (False → p5))) ∧ True) → (p2 ∧ (p4 ∧ (p1 ∧ (p4 ∨ (p1 ∨ False)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350106055454289273501325822768 : (p4 → (((((((False → (p1 ∨ True)) → (p4 → p4)) ∧ (p2 ∨ p4)) ∨ (p4 ∨ p4)) → (False ∨ True)) ∧ (p3 ∨ ((True ∧ False) ∧ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184332383679809876877023358658 : (((True ∧ ((False ∧ ((p2 ∨ p4) ∨ p4)) ∨ (p5 → True))) → p3) ∨ (((p2 ∨ (False ∧ p1)) ∨ True) ∨ (((p4 ∧ (p3 → p5)) ∨ p2) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191484344601633284920917096886 : ((True ∧ ((p3 ∧ p2) ∧ ((p1 → p5) → (p1 ∨ p2)))) ∨ ((p4 ∧ p1) → ((p4 ∨ p2) ∨ (p3 ∧ ((True → p3) ∧ ((p4 ∧ p2) ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135651226504246482492623982304 : (((((p2 → (p2 ∧ (p3 ∧ True))) → p1) → (((p1 ∧ p3) ∨ p4) ∧ (p4 ∧ p1))) → ((False ∨ (p3 ∨ p2)) ∨ p4)) ∨ ((p4 → p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251344955688087826854642691603 : ((p2 → p3) ∨ (p2 → (True ∧ (p2 ∧ ((((p4 ∨ (p2 → p4)) ∧ (p1 ∧ p2)) ∧ (True → (p1 ∨ p4))) ∨ ((p2 ∨ True) ∨ (True ∧ p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216051978153234576283946779560 : ((p5 ∨ (p4 ∧ (p1 ∨ p2))) ∨ (((p4 ∨ p2) ∧ p3) ∨ ((True → (((False ∧ ((False ∧ p2) ∧ False)) ∧ ((p4 ∨ False) ∧ p1)) → p1)) ∨ p5))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_444140364826873682068839247580 : (((((p5 ∨ p5) → (((True ∧ ((True ∨ ((p4 → (False ∨ True)) ∨ p2)) → (p2 ∧ p1))) ∧ False) ∨ (p3 ∨ p4))) ∨ ((p4 → True) ∨ p2)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711733292645832455604977089089 : ((((((False ∨ (False ∧ p1)) ∧ p5) ∧ True) ∨ ((p4 ∨ (((p1 → (False ∨ ((p1 ∧ p5) ∧ p3))) ∧ (p1 ∧ False)) → p2)) ∨ (p2 ∨ p4))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52634180038643000199779535368 : ((((p1 ∧ p1) ∨ ((p1 ∧ (p1 → (p3 → (p4 ∧ (p2 ∨ p2))))) → p5)) ∨ ((((p1 → p3) ∨ (p3 ∧ p3)) → False) ∨ (p5 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300545714974190467510789758427 : (False ∨ (((((((True ∧ (p3 → True)) ∨ (p5 → (p5 ∨ p4))) ∨ p2) → False) ∧ (p2 → p3)) ∨ (p1 ∨ p5)) ∨ (True ∨ ((p4 ∨ p3) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173589189765432635913948114253 : (((p1 ∧ (((p4 ∧ p2) → p3) ∧ ((((p2 → True) → False) ∨ p3) → True))) ∧ p5) → ((p1 → (False ∧ p3)) → ((True ∨ p2) → (p4 ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h1.left
    let h16 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h21 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h22 := h2 h21
    -- We need to get the left conjuct of h22 based on <expert-advice>.
    let h23 := h22.left
    -- False on the left can always be used.
    apply False.elim h23
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h1.left
    let h26 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h27 := h25.left
    let h28 := h25.right
    -- Conjunctions on the left can always be decomposed.
    let h29 := h28.left
    let h30 := h28.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h31 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h27
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h32 := h2 h31
    -- We need to get the right conjuct of h32 based on <expert-advice>.
    let h33 := h32.right
    -- One of the premise coincides with the conclusion.
    exact h33
  case inr h34 =>
    -- Conjunctions on the left can always be decomposed.
    let h35 := h1.left
    let h36 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h37 := h35.left
    let h38 := h35.right
    -- Conjunctions on the left can always be decomposed.
    let h39 := h38.left
    let h40 := h38.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h41 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h37
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h42 := h2 h41
    -- We need to get the right conjuct of h42 based on <expert-advice>.
    let h43 := h42.right
    -- One of the premise coincides with the conclusion.
    exact h43



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737378855166611611276295086457 : ((((p4 → p3) ∧ ((p5 → ((p4 ∧ p5) ∨ (p1 → p1))) ∧ (p2 ∧ ((p1 ∧ (((p1 ∨ ((p2 ∧ p4) ∨ False)) → False) ∨ False)) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315881927102132608479284286453 : (p3 ∨ (True ∧ (((p4 → (p2 → True)) ∧ (False ∧ (p2 ∧ (((p4 → False) ∨ p1) ∨ (p2 → ((p1 → ((p4 ∧ p2) ∨ p2)) → p2)))))) ∨ True))) := by
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
theorem thm_5_vars_476498268266678945813072448076 : (((((p3 ∧ p2) ∧ ((p4 → True) → (p5 ∧ (p5 → False)))) ∨ (((p5 ∨ True) ∨ ((p1 ∨ (p5 ∧ ((False → p2) → p2))) ∨ p3)) ∨ p1)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258775694634540080110127754434 : ((True → False) → ((((True ∧ ((p4 ∧ (p1 ∨ ((p4 → (False ∧ p5)) → True))) ∧ p3)) ∧ p1) ∧ (p1 ∧ (p1 → (p2 ∨ p5)))) ∨ (True → p1))) := by
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
theorem thm_5_vars_696554146448762156020934140981 : ((((((((p4 ∨ p5) ∨ False) ∨ ((p1 ∧ p5) ∨ p3)) ∧ p1) ∨ True) ∧ ((((p2 ∨ (p2 → p4)) ∧ ((p1 ∧ p5) → True)) ∨ p1) ∨ True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148165784019634665362287897076 : (((((p1 ∨ p4) ∨ (p3 ∧ ((p4 ∧ (False → (p5 ∨ (p3 ∧ False)))) ∨ p1))) ∧ p3) ∧ (p4 → (p2 ∨ p1))) ∨ ((p2 ∧ p5) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233859558769226255261644379336 : ((p4 ∨ (p4 ∧ p4)) → (((((((False ∨ ((p1 ∨ p4) ∨ p4)) → False) ∨ True) ∧ p4) ∧ False) ∧ p1) ∨ (((True → True) ∧ (p4 ∨ p4)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757361933963138573440184497481 : (((p1 ∧ ((p3 ∧ True) → (((False ∨ p1) ∧ p3) ∨ (((True ∧ p3) ∧ p2) ∨ (((((p2 ∨ (p3 ∧ True)) ∧ p2) → p4) ∧ p3) ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52048329494838019114976026511 : (((p1 → ((p1 → False) ∨ (p5 ∨ ((True → ((p2 ∨ False) ∨ (p5 → p5))) → p5)))) ∨ (p3 → (p2 → (p2 ∨ (False → (p4 → p5)))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792330041605752059898624257730 : (((True → ((((p5 → (True ∨ p4)) → False) ∧ ((p5 ∨ (p3 ∨ ((p3 → p1) → p3))) ∧ p1)) → ((p2 ∨ (True ∧ p3)) → (p4 ∨ p5)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    let h5 := h2.left
    let h6 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h12 : (p5 → (True ∨ p4)) := by
          -- Implications on the right can always be decomposed.
          intro h13
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h14 := h5 h12
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h16 : (p5 → (True ∨ p4)) := by
          -- Implications on the right can always be decomposed.
          intro h17
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h18 := h5 h16
        -- False on the left can always be used.
        apply False.elim h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h2.left
    let h23 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h26 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h26
    case inr h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
        have h29 : (p5 → (True ∨ p4)) := by
          -- Implications on the right can always be decomposed.
          intro h30
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h22, we can now drive its conclusion.
        let h31 := h22 h29
        -- False on the left can always be used.
        apply False.elim h31
      case inr h32 =>
        -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
        have h33 : (p5 → (True ∨ p4)) := by
          -- Implications on the right can always be decomposed.
          intro h34
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h22, we can now drive its conclusion.
        let h35 := h22 h33
        -- False on the left can always be used.
        apply False.elim h35
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299273306852874445488791516458 : (False ∨ ((((((p5 → (p3 ∧ p1)) → p5) → p1) ∨ (p4 → ((True ∧ (p5 ∧ False)) ∧ True))) → (p3 ∨ (False ∧ (p3 → (True ∨ p4))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773315536471319076554224967530 : (((False ∨ (((p5 ∧ p2) ∨ ((((((p5 ∨ (p5 → p4)) ∧ False) ∨ True) ∨ True) ∧ p4) ∧ (p5 → (((p1 ∧ False) ∨ p4) ∧ p5)))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178501639545901495421287288775 : (((p2 ∨ (p1 ∨ ((p3 ∧ (p5 ∧ p1)) ∨ p4))) ∨ ((p4 ∨ p1) → True)) ∨ ((((p4 ∨ (p2 ∨ True)) ∨ False) ∨ (False → False)) → (p4 ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225230574696279543172188743795 : (((p5 ∧ p3) ∧ False) ∨ ((p3 → (False ∧ (p5 ∧ (p5 ∨ True)))) → (((p2 ∧ (p4 ∨ True)) → (p5 ∨ (True ∧ p3))) ∨ ((p3 ∨ False) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204760930245882080649016436479 : (((((False → False) ∧ p4) ∧ p2) → False) ∨ (p1 → (((p3 ∨ (p3 ∨ ((((((False ∧ p3) → p5) ∧ True) ∨ p2) ∨ p2) ∧ p2))) ∨ p1) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257235481197976599353889092584 : ((p2 ∨ p2) → (p2 → ((p5 ∨ ((p2 ∨ (False ∨ True)) ∧ (((p1 ∨ (True ∨ (p4 ∨ p2))) ∨ p5) ∨ p3))) ∧ (False ∨ (False → (p4 → p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
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
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164582232603343532290570139743 : ((((p3 ∧ False) ∧ ((p5 → (((p2 → False) ∧ True) ∨ (p5 ∧ p4))) ∨ (False ∧ p2))) ∧ False) ∨ ((p5 → p2) → ((p3 ∧ (p2 ∨ p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304725909379699340368120785214 : (p1 ∨ (((p1 ∧ ((p3 ∨ (p2 → (p1 ∨ (p5 ∨ ((p2 → p5) → p2))))) ∧ p5)) ∨ ((((p1 ∧ p4) ∨ True) → p2) → True)) ∨ (p3 ∨ False))) := by
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
theorem thm_5_vars_46322528437415521936914271212 : (((((p5 → p2) ∨ (p5 ∧ (False ∧ ((p4 ∧ ((p5 → True) ∧ p4)) → (True ∨ p2))))) ∨ ((p4 ∨ (p1 ∨ p4)) → p5)) ∧ (p3 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119810815303756036429641915266 : (((((p5 → (p4 → ((((p3 → p1) ∧ (p2 → True)) → p3) ∧ (p5 ∨ False)))) ∨ (p4 → (True → (False ∨ p4)))) → p1) ∧ p5) → (False ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 → (p4 → ((((p3 → p1) ∧ (p2 → True)) → p3) ∧ (p5 ∨ False)))) ∨ (p4 → (True → (False ∨ p4)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_27703330287846475044882993285 : (((p2 ∨ p2) → ((((False ∨ (p2 → (False ∧ (p1 → (p2 → p2))))) ∧ True) → ((p4 ∧ (((p5 ∧ p4) ∧ p5) → p4)) ∨ p3)) ∨ p2)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790580616221394211684264798396 : (((p5 ∨ (p2 ∨ (p1 ∧ ((p1 → (((p3 ∧ False) ∧ (p3 ∧ p3)) → (p5 ∨ (False ∧ False)))) ∧ (p1 ∨ (((p2 ∧ p1) → True) → p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134896980296246265699642883570 : (((p5 → (False ∧ (((((False ∨ (((p1 → True) → (p5 ∨ p2)) ∨ False)) → p2) ∨ p5) → p5) ∧ (p1 ∨ p1)))) → False) ∨ (p1 ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67518656125750132747680356085 : ((p1 → (((p2 ∨ p4) → ((p3 ∨ True) ∧ False)) ∨ ((p4 ∧ p1) ∧ (p5 ∧ (p5 ∨ (True → (((False → (p5 ∧ True)) → p5) → p4))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68281090611374196182383245489 : ((p3 → ((True ∨ ((p1 → (p5 ∨ p5)) ∧ (((False ∨ ((((True ∨ (p2 ∨ p3)) ∧ p5) ∧ p4) → p3)) ∧ p2) ∨ False))) → (False ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773654611739435237828584558508 : (((False ∨ ((p5 ∨ (p2 → (((p2 → (p4 ∧ (p4 → (p5 ∨ (False → (p3 ∧ p3)))))) ∧ (p3 → False)) ∨ (False ∧ (p4 → p5))))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765750579514292678618340708120 : (((p4 ∧ ((p5 ∨ ((True ∨ (p4 ∧ (True ∨ (False → p1)))) ∨ p3)) → ((p4 → True) → ((((p4 ∨ False) ∧ p1) ∧ p3) → (p2 → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669270215363206914117531749760 : (((((p1 → (((p1 ∧ (False ∨ False)) ∨ ((p5 ∨ ((((p4 → p3) ∧ p2) ∨ False) ∨ p3)) → True)) ∨ p3)) → p1) ∨ (p3 ∧ (False ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612543900349926168619014787355 : ((((((((((p4 ∧ p5) → (True ∧ (p1 ∨ p4))) ∨ ((p3 ∨ p2) → ((False → p1) → p2))) ∨ p2) ∧ p3) → False) ∨ (p1 → p5)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_708596804539024865077187101710 : (((((p4 ∧ ((True ∧ (p1 → p1)) ∧ p3)) ∨ p1) → ((False ∨ ((p5 ∧ (p2 → p5)) ∧ False)) ∧ ((p1 ∨ ((p2 ∨ p5) → True)) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305918271967942087740625503370 : (p1 ∨ (((True → False) ∨ (False ∧ (p5 ∨ p5))) → ((p2 ∨ p3) → (((True ∧ p4) ∨ ((False → ((p2 → (p2 ∨ p2)) → False)) ∧ False)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h6
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h11 := h9 h10
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182895299791257673376202326517 : ((((True ∨ False) ∧ p1) → (True ∨ (False → ((p5 ∨ p4) ∧ p1)))) ∧ (((p1 ∨ (((True ∧ (True ∨ (True → p5))) → True) ∨ p3)) → p4) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55287150204682423213476636682 : (((p1 ∧ (p2 ∧ ((True ∨ p4) → p5))) ∨ ((p3 ∨ p5) ∧ (((p5 ∨ p5) ∨ p3) → (p5 ∧ ((((p1 ∨ p3) ∨ p2) → p4) ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730132389482347606106892285984 : (((((p4 ∨ p4) → False) → ((((p3 → p5) ∧ (p2 → ((False ∨ p3) → p5))) ∧ (p5 → p1)) ∨ (((False ∨ (p3 ∨ p5)) ∧ p5) → True))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337756434629930016090622556948 : (p1 → ((((((p3 → p1) → (p3 ∧ p2)) ∧ (True ∧ ((p1 ∧ p1) → p1))) ∧ True) ∨ p2) ∨ ((True ∧ ((p1 ∧ p4) → False)) ∨ (p1 ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754490084269478924655197193249 : (((False ∧ (False ∧ (((True → p2) ∧ ((p5 ∨ (True ∨ True)) ∧ ((p5 → p3) → ((p4 ∧ ((p3 → p1) ∧ (p2 ∨ False))) ∧ p5)))) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114983487985867126959986978362 : ((((((((p1 → True) → False) ∨ (True ∨ p3)) ∨ p4) ∧ p5) → p4) ∧ (p4 ∧ ((((p3 ∧ p5) ∧ (p2 ∧ p5)) ∨ False) ∧ p1))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662534479971905027412078340404 : ((((((p2 → p5) → (p3 → (p4 ∨ False))) ∨ (True ∨ (p2 → ((p4 ∨ (p2 ∨ ((p4 → (p2 ∧ p4)) ∧ False))) → False)))) → (p5 ∨ True)) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157445335405665652075178442425 : (((True → ((True ∧ False) ∧ ((((True ∧ p2) → ((False ∨ p5) ∨ False)) ∨ p4) → p5))) ∧ (p4 ∨ p1)) ∨ ((True ∨ p2) ∨ ((False ∨ p3) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317141303293534657390761998858 : (p3 ∨ (p5 → (p4 ∨ ((((p5 → ((True → (True ∧ p4)) ∧ p2)) → p4) ∧ ((True → p5) → (True → p4))) ∨ (((p5 → p1) ∨ True) ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667977028338808188419255559597 : ((((p3 ∨ (p4 ∨ ((((p2 ∨ ((((p4 ∨ p1) → p2) ∨ (p5 ∧ p4)) ∧ p3)) ∨ False) ∨ p3) → (p4 ∧ p1)))) ∧ ((p4 ∨ False) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225832086764260727814028111786 : (((True ∧ p5) ∨ False) ∨ ((((((p3 ∧ (True ∨ False)) ∨ p4) ∨ p4) → (p1 ∧ (p5 ∧ ((p3 → p1) ∨ True)))) ∨ True) ∧ ((p3 → True) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326822038306502787198404673300 : (True → ((((True ∧ (((((False ∧ (p2 ∧ (p2 → p1))) ∧ False) ∨ ((False → p4) ∧ (p5 ∨ (p3 ∨ False)))) ∧ p4) ∨ p5)) ∧ True) ∧ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135003655655142022995323769618 : (((p5 ∧ ((p4 ∧ ((p4 ∨ ((True → False) ∨ p5)) ∨ False)) → (p1 → ((p3 ∧ (False ∧ p5)) ∨ True)))) ∧ (p3 → p1)) ∨ ((False ∧ p3) → p2)) := by
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
theorem thm_5_vars_163744897041400802788314725961 : (((p1 → p3) → ((((p5 ∨ (p3 ∨ (p1 ∧ p1))) ∧ (p2 → p5)) ∧ (p5 → p3)) ∨ True)) ∧ (((p1 ∨ ((p3 ∧ p2) → True)) ∧ True) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1758499794307049441326026046 : ((((((p4 ∧ (p1 ∨ (((p1 ∧ False) ∨ p4) ∨ (p3 ∨ (p3 ∨ (False → p3)))))) ∧ p3) ∨ True) → False) ∧ True) ∨ ((p5 ∧ p5) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135557267411188037878319043660 : (((p3 ∧ (True → ((((p3 → p5) ∧ True) ∧ (True → (False ∧ p1))) ∧ (p2 → p3)))) ∧ ((p5 ∨ (p2 ∨ p4)) ∨ p1)) ∨ (p5 → (p5 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



