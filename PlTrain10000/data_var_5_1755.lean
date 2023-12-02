variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172539652706709839427481027981 : ((((p4 ∧ p3) ∧ p4) ∨ ((False ∧ ((p3 ∨ p4) ∧ (False → (False ∨ p3)))) ∧ p1)) ∨ (p4 → (((p3 ∨ (p3 ∨ False)) ∧ (p4 → p5)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306509269724289546931597883002 : (p1 ∨ ((True ∧ True) → ((p5 → True) → (True → ((p5 ∨ ((p5 ∨ ((p3 ∨ (True → p5)) ∨ False)) ∨ (p1 → ((p1 ∨ False) ∨ False)))) ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2466021573961340847575771040 : (((True → p2) ∨ (p4 ∧ ((p2 → p4) ∧ (p3 ∧ p2)))) ∨ (((p2 ∧ (p4 ∧ False)) ∧ p1) ∨ (p3 ∨ ((p2 ∧ (False ∧ True)) → False)))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62569850376552619645982597412 : ((p3 ∧ (True → ((p3 ∨ p2) ∧ (((p1 ∨ p1) ∨ (((p2 → (p3 ∨ p1)) → True) ∧ (((p5 ∧ (p4 ∨ p5)) ∨ p2) ∧ p3))) ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741730679847709149479970833164 : ((((True → p2) ∨ (((((False → False) → ((((p2 → False) → ((p3 ∧ ((p4 → p1) → False)) ∨ p2)) ∧ p2) ∨ p3)) → p5) ∨ True) ∨ p5)) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316488705932414814521921361916 : (p3 ∨ (p2 ∨ (((False ∨ ((((p3 ∨ p3) → p2) ∨ p4) → True)) ∧ (((((True ∧ p2) ∨ (p2 → False)) ∧ True) ∨ True) ∧ (True ∨ p3))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165767697546129379210524348390 : (((((p4 ∧ False) → True) ∨ False) → ((((p2 → p3) ∨ (p3 ∧ False)) ∧ p3) ∨ (p5 → p1))) ∨ ((p3 → p5) → ((p4 ∨ (p5 → p5)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134090456414624178914166977979 : (((((True ∨ p3) → (True ∧ (((((p4 → p2) → p3) → (False ∧ (p1 ∧ p4))) ∨ (True ∨ True)) → p3))) → p1) ∨ p5) ∨ (p2 → (True → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225331427727256232764060998669 : (((p1 ∨ False) ∧ False) ∨ (((p2 → (p5 ∨ (((p3 ∧ (p4 → ((False ∨ p3) ∨ p1))) ∧ ((False → True) ∧ (False → False))) ∧ True))) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616649494993452484206236163178 : (((((False ∨ ((p4 → (p3 → p1)) ∧ (p5 ∧ (p4 ∨ p4)))) ∧ ((False ∧ p3) ∧ (p2 → (True ∧ (p3 → (True ∨ (p3 → p5))))))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43678225671951313282181638737 : (((((p2 ∨ (((p5 → (((p2 ∧ p4) → p4) → p2)) → p5) → p4)) ∧ (True → (((p3 ∨ p2) ∨ (p3 ∧ p1)) ∧ p5))) → p1) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202682463865908122432199090514 : (((p5 ∧ (False ∨ False)) → (True ∨ p5)) ∧ (((((p4 ∧ p1) ∨ p2) ∨ False) ∨ (p4 ∨ (True ∨ ((p5 ∧ True) → ((p1 → p5) ∨ p1))))) ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h5
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200284574193721315837282502772 : (((p3 → (p1 ∨ True)) → (p1 ∧ (p2 → p5))) → ((p1 ∨ False) ∨ (((p4 ∨ ((False ∧ (p4 ∨ p5)) → ((p5 ∨ p5) ∧ p2))) → p3) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → (p1 ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115271062191248780451799008183 : (((p4 ∧ (p5 ∨ ((p3 → p5) ∨ (False → (True ∧ p1))))) ∨ (p3 → ((((((True ∨ p5) ∧ p4) ∧ False) ∧ p5) ∧ p2) ∨ p3))) ∨ (False ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148915112985095782929372077239 : (((((p3 → False) ∧ p3) ∨ p2) → ((((((p1 ∧ False) ∨ (p2 → False)) ∧ True) ∧ False) ∨ (p3 ∧ p2)) ∧ p2)) ∨ (((p5 ∧ False) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158334199461502213753473504144 : (((p1 ∧ True) ∧ (p4 ∨ ((p2 → (False ∧ True)) ∧ ((p2 ∨ (p3 → p5)) → ((p4 ∧ False) → False))))) ∨ (p3 ∨ (p3 → (p2 ∨ (p5 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618231084760928969654750168883 : ((((((True ∧ (p1 ∧ p4)) ∨ False) ∨ ((((((True ∧ (True → p4)) → p3) ∨ (p4 ∧ (p1 → (True ∧ False)))) ∧ False) ∨ p5) ∧ p4)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313067243072702925916740595622 : (p3 ∨ (((p3 → (True → ((p5 ∧ (((p4 → ((p3 ∨ (p3 ∧ p2)) → (False ∨ (True → (p4 ∨ p3))))) ∨ p4) → False)) ∧ p3))) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134070967360771296639850589594 : ((((((p1 → (p5 ∧ False)) → (((True ∨ (True ∧ p1)) ∨ (False → ((True → True) ∨ True))) ∨ True)) → p4) → p5) ∨ p2) ∨ ((p1 ∧ False) → False)) := by
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
theorem thm_5_vars_112680949605348755050147246379 : ((((True ∨ ((False ∨ (((p5 ∧ p3) ∨ False) → (False ∨ p5))) ∧ (p5 ∨ (p5 ∧ (p2 ∧ p1))))) → (p2 ∨ (p2 ∨ p1))) → p1) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219856525847960913558504339645 : ((p3 → (p5 ∧ (p2 → p4))) → ((((p5 ∨ (p3 ∧ (False ∧ True))) ∨ p5) → p3) ∨ ((False → (False ∧ (((p4 ∨ p3) → p3) ∧ False))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257441626124748020428099855417 : ((p3 ∨ True) → (((p5 ∧ True) ∨ (((p5 ∨ (p1 ∨ p2)) ∨ p2) ∧ ((False ∨ (((p5 ∨ p4) → p5) ∧ (p1 ∧ True))) ∧ p5))) → (p4 ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
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
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h10.left
        let h14 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h15 =>
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h21 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h22 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h10.left
          let h26 := h10.right
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h27 =>
            -- False on the left can always be used.
            apply False.elim h27
          case inr h28 =>
            -- Conjunctions on the left can always be decomposed.
            let h29 := h28.left
            let h30 := h28.right
            -- Conjunctions on the left can always be decomposed.
            let h31 := h30.left
            let h32 := h30.right
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h33 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h34 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
        case inr h35 =>
          -- Conjunctions on the left can always be decomposed.
          let h36 := h10.left
          let h37 := h10.right
          -- Disjunctions on the left can always be decomposed.
          cases h36
          case inl h38 =>
            -- False on the left can always be used.
            apply False.elim h38
          case inr h39 =>
            -- Conjunctions on the left can always be decomposed.
            let h40 := h39.left
            let h41 := h39.right
            -- Conjunctions on the left can always be decomposed.
            let h42 := h41.left
            let h43 := h41.right
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h44 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h45 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
    case inr h46 =>
      -- Conjunctions on the left can always be decomposed.
      let h47 := h10.left
      let h48 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h47
      case inl h49 =>
        -- False on the left can always be used.
        apply False.elim h49
      case inr h50 =>
        -- Conjunctions on the left can always be decomposed.
        let h51 := h50.left
        let h52 := h50.right
        -- Conjunctions on the left can always be decomposed.
        let h53 := h52.left
        let h54 := h52.right
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h55 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h56 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698785104725173493265212276064 : (((((p1 ∧ p5) → (p2 ∨ (p4 ∧ ((True ∨ (False → p1)) → p4)))) ∨ (True ∨ ((True ∧ p4) → ((True → (p3 ∨ (p4 → p1))) → p4)))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_166757993855454141510048453851 : ((p4 → (p2 ∨ ((p5 → (((p4 → p2) ∨ False) ∧ (p5 → (p1 ∧ True)))) ∨ (p2 ∧ False)))) ∨ (p1 → ((p4 → p1) → (True ∨ (p2 ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305455143024154892260815787726 : (p1 ∨ ((p2 → ((p4 → (p4 ∧ False)) → ((((p4 ∨ p1) ∧ p4) ∧ False) ∨ (False ∨ False)))) → (True → (((True → p4) → False) ∨ (False → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124944674854067419185506937482 : ((((False → False) → (p2 ∧ p4)) → (False ∨ ((p5 ∨ True) → ((((p4 → (p4 ∧ p5)) ∨ p1) ∧ p2) → ((p1 ∧ p1) ∨ p4))))) → (p2 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149844574051104496841293706388 : ((p1 ∨ ((p1 ∨ False) → ((p2 ∧ (p5 ∧ (p1 ∨ p1))) ∨ ((p5 ∧ p1) ∨ ((p1 ∧ True) → (False ∧ p1)))))) ∨ (True → (True ∨ (p4 ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148369911162368130426702181554 : ((((((p5 ∧ (p5 ∨ (p5 → p3))) → (p2 ∨ p4)) → (p2 ∧ False)) ∨ False) ∨ (((p2 ∨ True) ∨ p3) ∨ p2)) ∨ (p3 → (p3 → (p5 ∧ p1)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159304927784278464592050836990 : ((p5 → (((((p3 → (False ∧ ((p5 ∨ (False ∧ p2)) → (False ∧ p1)))) → False) ∨ p2) ∧ p3) ∨ p1)) ∨ ((True → (True ∨ (p2 ∧ p3))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172294476180147841387898943254 : (((((p3 ∧ (p4 ∨ p3)) → (p1 ∧ False)) ∨ p5) → ((p1 ∧ p3) ∨ (False → False))) ∨ (((p3 → p5) → (p2 ∨ ((p3 ∨ p3) ∨ p3))) ∨ p5)) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118222342219877600751721944339 : ((p1 ∨ ((((True → (((p5 → p2) ∧ (p2 ∨ p2)) ∧ p3)) ∨ p3) ∧ ((p1 ∨ (p2 ∨ p5)) ∧ ((p1 → False) ∨ p1))) ∨ False)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136222247175539554581519479805 : ((((p1 ∨ (p2 → (True ∧ p4))) ∨ False) ∨ (p1 → (p2 → (((p3 ∨ p5) → ((p2 → (p4 → p5)) ∧ p2)) → p3)))) ∨ (True → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773418945436646435263345404256 : (((False ∨ ((((p4 ∧ ((True ∨ (p2 → False)) ∧ p2)) ∨ (((p1 ∧ p3) ∨ (((p5 ∨ False) ∧ False) ∨ p5)) → (p1 ∧ p2))) ∧ p3) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64057111277011312975288468354 : ((False ∨ ((((p5 ∨ (p4 ∧ (p2 → (p3 ∨ p5)))) ∧ (True → p2)) ∨ (((False ∧ p3) ∨ True) → p5)) ∨ (((p2 ∧ p4) ∧ p1) ∨ True))) ∨ p1) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161399021042926017103481096721 : ((p1 ∧ ((p3 → (p3 → p5)) → (p2 ∧ (p4 ∧ (((p4 ∨ p5) → p2) ∨ (p4 ∨ (p3 → p4))))))) → (p3 → ((p5 → p3) ∧ (p2 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51050997212804128120173183430 : (((p3 ∨ (False ∧ ((((True → p1) → True) ∧ p3) → (p2 ∧ (True ∧ (p2 ∨ (False → p2))))))) ∧ ((((True ∧ p5) ∨ p1) ∧ p5) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344621161846677384347618041408 : (p2 → (p1 → (((p3 ∨ p5) ∧ p2) → ((p1 → False) → (p1 ∧ (p5 → (((p4 ∨ p5) ∧ (p5 ∧ True)) → ((p5 ∨ p3) → (False ∧ p4))))))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Implications on the right can always be decomposed.
  intro h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h10.left
    let h14 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h14.left
      let h17 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h3.left
      let h19 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h20 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h21 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h22 := h4 h21
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h24 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h25 := h4 h24
        -- False on the left can always be used.
        apply False.elim h25
    case inr h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h14.left
      let h28 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h29 := h3.left
      let h30 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h31 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h32 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h33 := h4 h32
        -- False on the left can always be used.
        apply False.elim h33
      case inr h34 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h35 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h36 := h4 h35
        -- False on the left can always be used.
        apply False.elim h36
  case inr h37 =>
    -- Conjunctions on the left can always be decomposed.
    let h38 := h10.left
    let h39 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h40 =>
      -- Conjunctions on the left can always be decomposed.
      let h41 := h39.left
      let h42 := h39.right
      -- Conjunctions on the left can always be decomposed.
      let h43 := h3.left
      let h44 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h43
      case inl h45 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h46 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h47 := h4 h46
        -- False on the left can always be used.
        apply False.elim h47
      case inr h48 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h49 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h50 := h4 h49
        -- False on the left can always be used.
        apply False.elim h50
    case inr h51 =>
      -- Conjunctions on the left can always be decomposed.
      let h52 := h39.left
      let h53 := h39.right
      -- Conjunctions on the left can always be decomposed.
      let h54 := h3.left
      let h55 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h54
      case inl h56 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h57 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h58 := h4 h57
        -- False on the left can always be used.
        apply False.elim h58
      case inr h59 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h60 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h61 := h4 h60
        -- False on the left can always be used.
        apply False.elim h61
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h62 =>
    -- Conjunctions on the left can always be decomposed.
    let h63 := h10.left
    let h64 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h63
    case inl h65 =>
      -- Conjunctions on the left can always be decomposed.
      let h66 := h64.left
      let h67 := h64.right
      -- Conjunctions on the left can always be decomposed.
      let h68 := h3.left
      let h69 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h68
      case inl h70 =>
        -- One of the premise coincides with the conclusion.
        exact h65
      case inr h71 =>
        -- One of the premise coincides with the conclusion.
        exact h65
    case inr h72 =>
      -- Conjunctions on the left can always be decomposed.
      let h73 := h64.left
      let h74 := h64.right
      -- Conjunctions on the left can always be decomposed.
      let h75 := h3.left
      let h76 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h75
      case inl h77 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h78 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h79 := h4 h78
        -- False on the left can always be used.
        apply False.elim h79
      case inr h80 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h81 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h82 := h4 h81
        -- False on the left can always be used.
        apply False.elim h82
  case inr h83 =>
    -- Conjunctions on the left can always be decomposed.
    let h84 := h10.left
    let h85 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h84
    case inl h86 =>
      -- Conjunctions on the left can always be decomposed.
      let h87 := h85.left
      let h88 := h85.right
      -- Conjunctions on the left can always be decomposed.
      let h89 := h3.left
      let h90 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h89
      case inl h91 =>
        -- One of the premise coincides with the conclusion.
        exact h86
      case inr h92 =>
        -- One of the premise coincides with the conclusion.
        exact h86
    case inr h93 =>
      -- Conjunctions on the left can always be decomposed.
      let h94 := h85.left
      let h95 := h85.right
      -- Conjunctions on the left can always be decomposed.
      let h96 := h3.left
      let h97 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h96
      case inl h98 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h99 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h100 := h4 h99
        -- False on the left can always be used.
        apply False.elim h100
      case inr h101 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h102 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h103 := h4 h102
        -- False on the left can always be used.
        apply False.elim h103



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52797851183071147624468548630 : (((((p5 ∧ (p3 → p3)) ∧ ((p2 ∨ p2) → p1)) ∨ (p2 ∨ (p3 ∧ p5))) → (((((p1 ∧ False) ∧ False) ∨ (p2 ∨ True)) ∨ p4) ∧ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
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
theorem thm_5_vars_133894064061786458623089693615 : (((False ∨ (((((p1 ∨ p5) ∧ p5) ∨ ((p2 ∨ p4) ∧ ((p2 → p5) ∧ p4))) → (p4 → False)) → (p1 ∧ p2))) ∧ p2) ∨ (p5 → (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653051351289628918223779599746 : ((((True → ((((True ∨ p3) ∧ ((p3 → (p3 ∨ p5)) ∧ (((p4 ∨ p5) → p2) → p3))) ∨ False) ∨ (p1 ∨ (p2 → False)))) ∧ (p1 → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40675486821684261395129344032 : (((((True → (True ∧ (((p2 ∧ (((p1 ∧ ((True → p3) → False)) → p4) ∨ False)) ∧ p1) ∧ p3))) ∧ (p2 ∨ (p1 ∨ p2))) → False) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112562811340492261310601901932 : ((((p2 ∧ (p3 → (p4 ∨ (p1 ∨ ((p2 ∧ p4) ∧ (p5 ∧ (((p4 → (p2 ∨ (p3 ∧ p5))) ∧ p4) ∧ p1))))))) → p5) → p2) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114504379186826605306426425231 : ((((False → (p1 → True)) ∧ (((p1 ∧ True) → ((True ∨ (p5 ∧ p4)) ∧ p1)) ∨ (p4 ∨ p1))) → (((p2 → p4) ∧ False) ∨ False)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112300810831054566114481536400 : (((p1 → (((True ∧ True) ∨ p4) → (True ∧ ((False → (p2 ∧ p3)) → ((((p4 ∧ True) ∧ (p5 ∧ p3)) → True) ∧ False))))) ∨ p3) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338172091082769486619598339363 : (p1 → (((p1 → p3) → (p4 ∧ (False → (p2 ∧ False)))) → (p1 → ((p3 ∨ (((False ∧ p2) ∨ (p2 → (True ∧ p2))) ∨ p5)) ∧ (True ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767226266406909699740887211990 : (((p5 ∧ (((p4 ∨ (((p2 → ((p2 ∧ p3) → ((False → p4) ∧ True))) → (p2 → (p4 → (p4 → (p1 ∨ False))))) ∧ p2)) ∨ p1) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317802266011813624325551386389 : (p4 ∨ ((((p3 → ((p2 ∧ (p4 ∨ p5)) ∧ p4)) → p4) → ((((p5 → ((p3 ∧ False) ∧ ((p2 ∨ p1) ∨ p4))) ∧ p2) ∧ p3) → p2)) ∨ p3)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255555014112540120176814010766 : ((p5 ∧ p3) → ((((((((True → (p5 ∨ (p1 → p5))) ∨ p2) ∧ p2) ∨ p2) → p5) → (((p2 → False) → p1) ∧ p3)) ∨ p3) ∧ (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14791316741560135644927078887 : ((((((p3 ∧ p3) → (p1 → (((p3 ∧ p2) ∨ p5) ∨ (p2 ∧ (p1 → p4))))) ∧ p1) → ((p4 → True) → (p2 → p4))) ∨ (p2 ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147367540647206702149051995795 : ((((False ∨ ((((True ∧ (p3 → (p1 ∧ p3))) ∨ p4) ∨ p3) → p3)) ∧ (False ∧ ((p2 → False) ∧ p5))) ∨ p3) ∨ (p3 ∨ (True ∨ (p5 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303746327131725726588031849920 : (p1 ∨ ((((p2 ∧ ((p4 → ((((((False ∨ False) ∧ True) ∧ p4) ∨ (p1 → False)) ∧ p1) ∧ p2)) ∨ (p5 ∨ (p5 → p2)))) ∧ p2) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344285587266164652566658646987 : (p2 → (p3 ∨ ((((p4 ∨ (p4 ∧ (((p3 ∧ p4) → (p5 ∧ True)) → p5))) ∨ (((p4 ∨ (p2 → p4)) ∧ p4) → (True ∨ True))) ∨ p5) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164979508101287486467532627248 : (((((p5 ∨ p4) ∨ ((p3 ∧ p1) → (p1 ∨ (True ∨ (p5 → p2))))) → (False → p4)) → p1) ∨ (p1 ∨ ((True → ((p1 ∧ False) ∨ True)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_44154264509830244106184032654 : (((((p4 ∧ (((False → p2) ∨ p1) ∧ (((((p4 ∨ p3) → (p3 ∨ p5)) ∨ p3) ∧ p4) ∧ p1))) → p3) → (p1 ∧ (p2 ∧ p1))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56868369623404275427090570670 : (((p1 ∧ (p5 ∧ p1)) ∧ (p3 → ((True ∨ p4) → (((p4 ∧ p2) ∨ (p5 ∨ True)) ∧ ((p2 → (p3 ∧ False)) → (p1 ∧ (p5 ∧ p3))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86612051065197063022299312487 : (((((p3 ∨ (p5 ∨ p3)) ∨ False) ∨ (p3 → p3)) ∧ ((p2 → (p5 ∧ (((p2 → p2) → (p3 ∧ (p3 ∧ (True → p5)))) ∧ True))) ∧ p2)) → p3) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h3.left
        let h8 := h3.right
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h3.left
          let h12 := h3.right
          -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
          have h13 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h12
          -- We have shown the premise of h11, we can now drive its conclusion.
          let h14 := h11 h13
          -- We need to get the right conjuct of h14 based on <expert-advice>.
          let h15 := h14.right
          -- We need to get the left conjuct of h15 based on <expert-advice>.
          let h16 := h15.left
          -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
          have h17 : (p2 → p2) := by
            -- Implications on the right can always be decomposed.
            intro h18
            -- One of the premise coincides with the conclusion.
            exact h18
          -- We have shown the premise of h16, we can now drive its conclusion.
          let h19 := h16 h17
          -- We need to get the left conjuct of h19 based on <expert-advice>.
          let h20 := h19.left
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h21 =>
          -- Conjunctions on the left can always be decomposed.
          let h22 := h3.left
          let h23 := h3.right
          -- One of the premise coincides with the conclusion.
          exact h21
    case inr h24 =>
      -- False on the left can always be used.
      apply False.elim h24
  case inr h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h3.left
    let h27 := h3.right
    -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
    have h28 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h27
    -- We have shown the premise of h26, we can now drive its conclusion.
    let h29 := h26 h28
    -- We need to get the right conjuct of h29 based on <expert-advice>.
    let h30 := h29.right
    -- We need to get the left conjuct of h30 based on <expert-advice>.
    let h31 := h30.left
    -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
    have h32 : (p2 → p2) := by
      -- Implications on the right can always be decomposed.
      intro h33
      -- One of the premise coincides with the conclusion.
      exact h33
    -- We have shown the premise of h31, we can now drive its conclusion.
    let h34 := h31 h32
    -- We need to get the left conjuct of h34 based on <expert-advice>.
    let h35 := h34.left
    -- One of the premise coincides with the conclusion.
    exact h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762041145199328888074824917218 : (((p3 ∧ ((p2 → (p2 ∧ ((p3 → p3) → (p2 ∧ ((p2 ∨ ((p2 → ((p2 → (False ∨ False)) ∧ (False ∧ p1))) ∨ p3)) → p4))))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114006622464500261829926576208 : (((((((p1 ∨ False) → ((p5 ∧ False) ∨ p3)) ∨ p5) ∧ (True → ((p2 ∧ (p4 ∧ p5)) ∨ True))) ∧ p3) ∨ ((p4 ∧ False) ∨ p2)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616901000318027810785729601 : ((((((((True ∧ p5) → False) ∧ ((p2 ∧ (((p4 → p5) ∨ (False ∧ p4)) ∨ True)) → p2)) ∧ p2) ∨ p3) ∨ p5) ∨ (p5 ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116618439661235552497152709095 : (((False → p1) ∧ ((True → (p5 → False)) → ((True → p3) ∨ (p3 → ((((p5 ∨ (p3 ∨ (p1 ∧ p5))) ∨ p2) ∨ p1) ∧ p2))))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344674452020746275530700372308 : (p2 → (p2 → ((((((p2 → True) ∧ p5) → (p3 ∨ p3)) ∨ p3) → p5) ∨ (((False ∧ ((False → p1) ∧ p5)) → True) → (p2 ∨ (p5 → p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199868938107552097396084751307 : (((False → (p2 → (p1 ∧ p4))) ∧ (p5 ∨ p3)) → (((((p2 ∧ p3) ∨ p1) ∧ p5) ∧ p4) → (p1 ∨ ((p3 → True) ∧ (p3 → (p4 ∧ p5)))))) := by
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
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h4
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h16
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h17
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h4
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h1.left
    let h20 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h22 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129355033094801194839286652253 : (((False ∧ ((p4 ∧ (p3 ∧ (p2 → p2))) ∧ (((p2 ∨ (p1 ∧ (p2 ∧ ((p5 → p4) ∨ p2)))) → False) → False))) ∨ True) ∧ (True ∨ (p2 ∧ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159019846790434864627068524611 : ((p4 ∨ (((False ∧ (p1 → p5)) ∧ ((True ∨ False) ∧ p3)) ∧ (True ∧ (((True ∨ p5) ∨ True) → p1)))) ∨ (p4 → ((p5 ∨ (False → True)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51900470031812945617112394517 : ((((p1 → (p4 → ((p1 → p4) → (False ∧ (((p1 → p2) ∨ True) ∧ p3))))) → p3) ∨ (((p2 → (p2 → p5)) ∨ (True → p2)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764026558541235342066505401337 : (((p3 ∧ (p1 → ((((p3 ∧ (p1 ∨ True)) ∨ p4) → p5) ∧ ((((False ∨ (False → p5)) ∧ (p5 ∨ (p5 ∨ False))) ∨ (p4 ∧ p4)) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57107602637612634706485182814 : ((((p1 ∨ True) ∧ False) ∨ (p5 ∧ (p1 ∨ (p5 → (True ∧ ((p3 ∧ ((((p3 ∧ p2) → True) ∨ (p2 → p4)) ∨ p3)) → (False ∨ True))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47040853564674494139938384292 : (((((p5 → ((p5 ∧ (p5 → p3)) → ((p5 → (p4 → False)) → p4))) ∨ (p4 → ((False ∧ p1) ∨ p2))) ∧ (p4 ∧ p2)) ∨ (p1 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209491339976207707280648242449 : ((p3 → (False ∨ ((p3 → p1) → p2))) → ((p1 ∧ ((p1 ∨ (p4 → False)) → p3)) → (((p4 ∧ p3) ∨ (p4 → (False ∨ (p2 ∧ p1)))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p1 ∨ (p4 → False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : (p3 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h14 := h11 h12
    -- One of the premise coincides with the conclusion.
    exact h14
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588395657764221076537698063112 : (((((((p2 → p3) ∧ p2) ∨ (((p5 ∧ False) ∨ ((True ∧ ((p2 ∨ False) ∧ (p1 → p1))) ∧ (p3 ∨ False))) ∨ (p2 → p2))) ∨ p3) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173236493456111937734679427092 : ((True → (((p1 → (True ∨ (p2 ∨ (p2 → p3)))) → False) ∧ (False ∧ (p2 → p4)))) ∨ ((p5 → p5) ∨ (p3 ∧ (False ∧ (p4 ∧ (False ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_36688288337781276342494933333 : ((p5 → (((p1 → p1) → (True ∧ ((True ∨ (p4 → p3)) → (((((p3 ∧ p4) ∧ p5) ∨ True) ∨ True) → ((p5 ∧ p1) ∨ p5))))) ∨ p4)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122593764248864687621250281586 : (((((p3 → (((True → False) ∧ p4) ∨ (((True → (p1 → p1)) ∧ ((p3 → p5) ∧ p5)) ∨ False))) → p5) ∨ p3) → (False → p5)) → (p5 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45729082437396616534051568744 : (((True → (p4 ∧ (p4 ∨ (((False ∧ p3) ∨ (p5 → False)) ∨ ((((p3 ∨ ((p5 → p2) ∧ True)) ∧ p3) ∧ (p2 → p5)) → p3))))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65643204039192707247698354735 : ((p4 ∨ (((p2 → (p5 ∧ (p3 ∨ p4))) ∧ (True → ((p3 ∨ False) ∨ (p3 ∨ (((p3 ∧ (True ∨ (p5 → False))) ∨ p5) → False))))) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66235744351641862333887612889 : ((p5 ∨ (((p4 → ((False ∧ p4) ∧ p2)) → (p5 ∧ p4)) → (((p1 ∨ True) → p5) → (((True → p5) ∨ True) ∨ (True ∨ (p3 ∧ True)))))) ∨ p1) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60610600721712233943987067860 : ((True ∧ (((((True → p2) → ((False ∨ (p1 → (p4 ∨ (p4 → p2)))) ∧ p3)) → (p2 ∨ ((p5 ∨ p5) → p1))) ∨ p2) ∨ (True ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158656374935885059296877779364 : ((p1 ∧ (p1 ∧ (((p2 → p3) ∧ p5) ∧ ((p3 ∧ (False → ((p1 → (False ∨ p5)) → p3))) → p1)))) ∨ (p1 → ((p2 ∨ (p5 ∧ True)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787443068638919080937321483501 : (((p4 ∨ (p5 ∧ ((False ∧ False) ∧ (((((p2 ∨ (((p3 ∨ False) ∧ (p5 ∨ (p2 ∧ p4))) ∧ True)) ∨ (False → True)) → p1) → True) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747773089782161770524302848806 : ((((False → p1) → (((p3 ∧ p1) ∨ False) ∨ (p1 ∨ (((p2 ∧ (p2 → p1)) ∨ False) → (((False ∧ True) ∧ (p1 ∧ p3)) ∨ (p3 ∨ p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765818217675504524389558685552 : (((p4 ∧ ((p1 → ((((True ∧ p3) ∨ p4) → p2) → p1)) → (True ∧ (((p4 ∨ (((p1 ∧ True) ∧ p1) ∧ p2)) ∨ False) ∧ (p5 ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149912782377644542892588324770 : ((p3 ∨ (((p1 ∨ p3) ∨ ((((True → p3) ∨ ((((p5 → True) ∧ True) → p4) ∨ True)) ∨ p1) ∨ p4)) ∨ p2)) ∨ (p5 → (False → (p5 ∧ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688139655018128372122571516722 : (((((p2 → (p3 ∧ p3)) ∧ ((True ∨ p5) → (((p4 ∨ (p5 → p2)) ∧ p5) ∨ p2))) ∧ (p2 ∨ (((False ∧ (p5 → False)) ∧ p1) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118605804684467674739577653969 : ((p4 ∨ ((True ∧ (((True ∨ True) ∧ ((p3 ∧ False) ∧ (False ∨ p5))) ∨ (True ∨ ((p4 → False) → p1)))) ∨ (False ∧ (p3 ∧ p4)))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67436185830143579422732004596 : ((p1 → (((p5 ∧ (p1 ∨ ((p1 ∧ p3) ∧ p1))) ∨ (((p2 ∧ p1) ∧ p5) ∧ (((p3 → True) ∧ p3) ∨ p1))) ∧ (p3 → (p3 → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656856229585344569442809266 : ((((p2 ∨ ((p1 → (p1 ∨ p3)) → (((False → (p1 ∧ False)) ∧ (p5 → p5)) → p2))) ∧ p2) ∧ (p1 ∨ ((p4 ∧ True) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322347136043128639133952246293 : (p5 ∨ (((p3 → ((p2 → (True ∨ ((True → p1) → p5))) → (False ∧ ((p1 ∨ p1) ∨ (((p3 ∧ p2) → p3) ∧ False))))) → (p5 ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39018922171390418873169271340 : ((((False → True) ∧ (((False → (p4 ∨ p2)) → ((p3 ∨ ((p5 ∧ False) ∧ (p5 ∧ p1))) ∧ ((p1 ∨ p1) ∧ p5))) → (p1 ∨ p2))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141277966723851704548921131623 : (((((False → p2) ∨ False) → p1) ∧ ((False → False) ∨ ((True → p2) → ((p4 → (p2 → p4)) → ((p1 ∧ p5) → False))))) → ((p5 ∧ p1) ∨ p1)) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((False → p2) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : ((False → p2) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h9
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_452658636829357391715025212665 : ((((p5 ∨ (((((p3 ∨ ((p3 → p5) → p2)) → (p4 → (p2 → (p3 ∧ p5)))) ∨ p4) ∨ True) ∨ p1)) ∨ ((p2 → p1) ∧ (True → p1))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160582133275414185099839864895 : (((False → (p1 ∨ (p3 ∧ (((p3 ∨ (False → p1)) → p4) ∨ False)))) → ((p4 ∧ (p1 ∧ p1)) ∨ False)) → (((p4 → (p5 ∨ p3)) ∧ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135613774565357998761446325551 : (((False ∨ ((p2 ∨ (((p1 → p5) ∧ p1) ∧ ((True ∧ (p1 ∧ p3)) → True))) ∧ True)) ∨ ((False ∨ p1) ∧ (p2 ∧ p2))) ∨ ((p2 ∧ p1) → p1)) := by
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
theorem thm_5_vars_190758882727950364127515772467 : (((p2 → (p1 ∨ (p3 ∨ (p1 → p3)))) ∧ (p4 ∧ False)) ∨ (p3 → (p5 → (((False → p2) ∧ p4) → (p4 → ((False → True) ∨ (True → False))))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308511850088413035912892399674 : (p2 ∨ ((((((p4 ∧ (p1 ∨ p3)) ∨ ((True → p3) → p3)) ∨ p1) ∨ (p1 ∨ (p2 → p1))) ∧ ((False ∨ (p1 → p2)) → (False → p3))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49623860121382754842169524871 : ((((((p3 → p3) ∧ (p1 ∧ p2)) → p4) ∧ (((p4 ∧ (p2 ∨ (((p4 → False) ∨ False) → False))) → False) ∨ p4)) → ((p1 ∨ True) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44394684499955716169964653212 : ((((p3 ∧ (((((p1 → (p1 ∧ True)) ∨ (True ∨ True)) → p5) ∨ p2) → False)) ∨ ((((p3 ∨ p3) ∧ (True ∨ p3)) ∨ p5) ∨ True)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82218423373260563834503596187 : ((((((p3 ∧ True) ∨ (p4 ∨ (p5 → (p4 ∨ p1)))) → ((p3 ∧ (p3 ∨ True)) ∧ (p5 ∧ False))) ∧ p2) ∧ ((p1 ∨ True) → (p4 ∨ p5))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : (p1 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : ((p3 ∧ True) ∨ (p4 ∨ (p5 → (p4 ∨ p1)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258939986587202421348912944012 : ((True → p3) → ((((True → (((p3 ∧ p5) → p2) → (((False ∧ ((p1 ∧ p2) ∨ p3)) ∧ p5) ∨ (p3 ∨ (p1 → True))))) → False) → p1) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True → (((p3 ∧ p5) → p2) → (((False ∧ ((p1 ∧ p2) ∨ p3)) ∧ p5) ∨ (p3 ∨ (p1 → True))))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h3
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321004723311640563522017909200 : (p4 ∨ (False ∨ (((p3 ∧ (p4 ∧ ((p5 → True) ∨ p5))) → (p2 → ((p4 → ((p3 ∧ p4) → (p3 ∧ False))) ∨ p3))) ∨ (p1 ∨ (p4 ∨ p2))))) := by
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
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42659489122608421011905681914 : (((p4 ∨ ((False → (p1 → ((False ∨ p2) → (((p5 ∧ (p3 → (False ∧ p5))) ∧ p2) ∨ p1)))) ∧ (((p1 ∧ True) → p5) → False))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



