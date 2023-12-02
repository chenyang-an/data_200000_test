variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47544203125132767405728591127 : (((p5 ∨ ((p5 ∧ (p5 → (False ∨ (False ∨ False)))) ∨ (((p1 ∧ (p5 ∧ (p3 ∧ ((p2 ∨ p2) ∨ True)))) ∨ p4) → False))) ∨ (True ∨ False)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68134800520936145096632879179 : ((p3 → (((p3 ∧ (p3 ∧ ((p5 ∨ ((((False ∨ p3) ∨ p4) ∨ ((p5 → True) → p2)) → (p5 ∧ (True ∨ p4)))) → p4))) ∧ False) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790198014754168472966322536294 : (((p5 ∨ (False ∧ ((((((p4 ∨ (True ∨ False)) ∧ (p5 → p1)) ∧ p4) ∨ ((p5 → p2) ∧ ((p1 ∧ False) ∧ p2))) → (p2 ∧ p5)) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126105291385071655597711442140 : ((True ∧ (((((False ∧ p3) → p5) ∧ (p3 → p2)) ∨ (((p2 ∨ (((p5 ∨ p3) ∨ False) ∧ p3)) ∨ True) ∨ p3)) ∧ (p2 → p4))) → (p1 ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h16 =>
            -- Disjunctions on the left can always be decomposed.
            cases h16
            case inl h17 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h18 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h19 =>
            -- False on the left can always be used.
            apply False.elim h19
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257023647522465711625598746309 : ((p2 ∨ True) → (((p3 ∧ (p1 → ((True → (p5 ∨ ((p1 ∧ p3) ∨ p4))) → p3))) ∧ p1) ∨ (p1 → (p1 ∨ ((p1 → p1) ∧ (p2 → p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798695025834070981362223726270 : (((p1 → (((p2 → (p2 ∨ False)) ∧ p1) → ((((p3 → (p4 ∧ p1)) ∧ (p1 → (p3 ∨ ((False ∨ p1) ∧ p4)))) ∨ p3) → (p4 ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739459101768858468398573761904 : ((((p5 ∧ False) ∨ ((((p5 ∧ (((p4 ∧ False) → p4) ∨ (True → (p5 ∧ False)))) ∨ (p4 → p1)) ∨ (p1 → False)) → (p3 ∨ (p4 ∨ True)))) ∨ False) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238013965693239473220306912370 : ((True ∨ p1) ∧ ((((True → p1) ∧ ((p5 ∨ (p4 ∨ p1)) → True)) ∧ (((p3 ∧ p3) ∨ False) ∧ p4)) ∨ ((p5 → (p4 ∧ p4)) → (p1 → p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326893352857122628860144669165 : (True → (((p3 ∨ (True → ((p5 ∨ (True ∧ True)) ∧ (p4 ∨ ((p5 → (((p4 → (p4 → (p2 ∨ p1))) ∧ True) ∨ p2)) ∧ False))))) ∨ True) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328852106701104074718151204830 : (True → ((((False ∨ (p1 → p1)) ∨ p3) ∨ (p4 ∨ p2)) ∧ (p5 ∨ ((((((True → p1) ∧ p3) ∧ p5) ∨ p4) ∧ p1) ∨ (p5 ∨ (p5 → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662023684166015452179230085495 : (((((False ∨ ((p3 ∨ ((False → p3) ∧ (p3 ∨ (False → p5)))) ∨ (p1 ∨ p1))) → (((p1 → p3) → p4) ∨ (p1 → False))) → (p2 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181572072827761702132946690610 : ((False → (p1 → (p5 ∨ (((p4 ∧ p3) → ((p1 → p4) → False)) → p2)))) → ((p5 ∨ (p4 ∨ (p2 ∨ (p1 → p1)))) ∨ (p2 → (p1 → False)))) := by
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
theorem thm_5_vars_126620596181506074719862145186 : ((p3 ∧ ((p5 ∨ p2) ∧ ((p1 ∨ (((p2 ∧ (((False → False) ∧ p1) ∨ p4)) → p5) ∨ (False → (p3 → p4)))) ∧ (p5 ∨ p5)))) → (p1 ∨ p5)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h15
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h5.left
    let h21 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h23 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h22
      case inr h24 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h22
    case inr h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h27 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h27
        case inr h28 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h28
      case inr h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h30 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h30
        case inr h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340771933079729885464495494285 : (p2 → (((((p4 ∨ ((((True ∧ ((p5 ∧ p1) ∨ p2)) ∨ True) ∨ ((p3 ∧ p3) → ((p2 ∧ p1) → False))) ∧ True)) → p5) ∨ False) → p3) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345318490626167167851090082944 : (p3 → ((((p4 ∨ (((p2 ∧ ((p5 ∨ (((p5 ∧ p5) → (p4 → ((p5 → p2) ∧ True))) ∨ p1)) → True)) → p1) ∧ True)) ∨ p3) ∧ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39846840553372839250683284642 : (((p1 → (((False ∧ (p1 → p1)) → (p2 → p3)) → ((False → ((True → ((False ∨ True) → (p5 → (p4 → p1)))) → False)) → p4))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55774071123418465183670680201 : ((((p4 ∨ p1) ∧ (p2 → p4)) ∧ (p4 ∨ ((((p2 → p5) ∧ p4) ∨ ((True ∨ (p3 → False)) ∨ ((True → p4) ∨ (p4 → p4)))) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44902256719519866538178043016 : ((((False ∨ (p4 ∨ p2)) → (((False ∧ ((p4 → p2) ∧ ((True ∧ (False ∧ True)) ∧ ((p5 ∨ (p3 ∨ p3)) ∨ p2)))) ∧ p5) ∧ p5)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661956554421016442058966567870 : ((((((p5 ∧ ((p2 ∨ p1) ∧ p3)) ∨ (p1 ∨ (((p3 ∨ p5) ∧ p3) → p3))) ∨ (False ∧ (((False ∨ True) ∨ p4) ∧ p5))) → (p1 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197933439459148404596072739089 : (((p5 → (p1 ∨ p2)) → ((p1 → p5) ∨ p4)) ∨ ((p1 ∧ p1) → (p1 ∨ (((((True ∨ p5) → True) ∨ (True ∧ p3)) ∨ (p5 ∨ True)) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193941081974103557005965960632 : ((p2 ∨ (((p2 ∧ (p1 → (True ∧ False))) ∨ False) → p2)) → (((p2 → p1) ∨ (((False ∧ p3) ∨ (p1 → True)) ∨ (p3 ∨ p5))) ∨ (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41568361830653014966418848301 : ((((True ∨ (False ∨ ((True ∨ p2) ∨ ((p3 ∧ p2) ∨ p3)))) → ((p3 ∨ (((p2 → False) ∨ (False ∧ (p5 ∨ p3))) ∧ p5)) ∨ True)) ∨ p3) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
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
theorem thm_5_vars_328106393453340051749500295000 : (True → ((((True ∧ p1) ∧ ((((False → (False ∧ False)) ∧ p4) → ((p5 ∧ (p2 ∨ p3)) → (p2 → p3))) ∧ p3)) → False) ∨ (False → (p1 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219357939768015851882164518353 : ((p3 ∨ ((False → p2) ∧ p4)) → ((((p4 ∧ p4) ∧ p4) ∧ (((((p1 ∨ p4) ∨ p3) → False) ∧ p4) ∧ (p4 ∨ ((p2 ∨ True) ∨ p4)))) → p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h4.left
  let h10 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h18 : ((p1 ∨ p4) ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h19 := h11 h18
      -- False on the left can always be used.
      apply False.elim h19
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h23 =>
          -- One of the premise coincides with the conclusion.
          exact h23
        case inr h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h24.left
          let h26 := h24.right
          -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
          have h27 : ((p1 ∨ p4) ∨ p3) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h26
          -- We have shown the premise of h11, we can now drive its conclusion.
          let h28 := h11 h27
          -- False on the left can always be used.
          apply False.elim h28
      case inr h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h30 =>
          -- One of the premise coincides with the conclusion.
          exact h30
        case inr h31 =>
          -- Conjunctions on the left can always be decomposed.
          let h32 := h31.left
          let h33 := h31.right
          -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
          have h34 : ((p1 ∨ p4) ∨ p3) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h33
          -- We have shown the premise of h11, we can now drive its conclusion.
          let h35 := h11 h34
          -- False on the left can always be used.
          apply False.elim h35
    case inr h36 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h37 =>
        -- One of the premise coincides with the conclusion.
        exact h37
      case inr h38 =>
        -- Conjunctions on the left can always be decomposed.
        let h39 := h38.left
        let h40 := h38.right
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h41 : ((p1 ∨ p4) ∨ p3) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h40
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h42 := h11 h41
        -- False on the left can always be used.
        apply False.elim h42



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201110295822608535048426669332 : ((True → (((p2 ∧ p4) → True) → (p4 ∧ False))) → ((p5 ∧ p3) ∨ (((True → ((False → True) ∧ (p5 ∧ p3))) → ((p2 ∨ p3) → p2)) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p2 ∧ p4) → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617458623245759485008026183521 : ((((((p1 → (p4 → (False → False))) ∧ p4) ∧ ((p3 → ((p3 ∨ (((False ∧ True) → p4) ∧ (True ∨ p1))) → p1)) ∧ (False → p4))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_61717345667137618230624514026 : ((p1 ∧ (True → (((p2 → False) ∧ ((p2 ∧ ((p4 ∨ p1) ∧ ((False → (p2 → p2)) → ((p3 → p1) → p4)))) → (False ∧ False))) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310682298082395191831299233052 : (p2 ∨ ((p3 ∧ ((p5 ∨ False) ∨ p4)) → ((((((False ∨ (p4 → (p3 ∧ p2))) → p5) ∨ False) → p2) ∨ (p3 ∨ (True → (True ∨ p5)))) ∨ p1))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621475016210862486076665390353 : ((((False ∧ ((((False → True) → (True → p2)) ∧ ((((True ∧ (p5 ∨ ((True → p2) → False))) → False) ∨ p2) ∨ (p1 ∧ True))) ∨ p3)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117700049900282715496760703494 : ((p3 ∧ ((p1 → p4) → ((False ∨ (((p1 ∧ (p1 → ((p5 ∧ p3) ∨ p4))) ∨ p5) ∧ ((p3 ∧ p2) ∨ False))) ∨ (False ∨ p4)))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42935961578256335062727833136 : (((p4 → (((((((p1 ∧ p5) ∨ p4) → p1) ∧ p3) ∨ (p2 ∧ (True ∧ False))) ∨ p4) ∧ ((p3 ∨ (True ∨ p4)) ∨ (p2 ∧ p5)))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138365576556109001226880450086 : ((p4 → (((p3 ∧ (False ∨ (False ∨ p5))) ∨ ((p1 ∨ True) ∨ (p5 ∨ (p2 ∨ p4)))) ∨ ((p1 ∧ True) → (p1 → True)))) ∨ (False ∨ (p5 ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674053160932480318125050915672 : ((((p1 ∧ ((p1 ∧ (p4 → False)) ∨ (((p4 ∨ p4) → False) ∨ ((True ∨ (False ∧ ((p1 → p3) ∧ False))) ∧ p4)))) → ((p2 → p1) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224375978107142916855677150802 : ((False → (p5 → False)) ∧ ((p4 ∨ True) → (True ∧ (p3 ∨ ((True ∧ (((p5 ∧ False) ∨ ((p1 ∨ p4) ∧ (False ∨ (p2 ∧ p4)))) ∨ True)) ∨ p2))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206489474791131047085396482449 : ((p5 ∨ (((p5 → False) ∨ p4) → p5)) ∨ ((p1 ∨ (True ∨ ((p2 ∨ True) ∧ ((True → True) ∨ p2)))) ∨ (True → (p3 ∧ (p4 ∨ (p3 → p2)))))) := by
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
theorem thm_5_vars_138378845372384522105126039533 : ((p4 → (((p1 → False) → False) → (((((True ∨ (False ∧ p3)) ∧ p4) → (True ∨ False)) → False) ∨ (p2 ∨ (p4 → True))))) ∨ (False ∨ (p5 ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199180427216951974452850299339 : (((p1 ∧ (p3 ∨ (p4 → (True ∧ True)))) ∧ p5) → ((True ∨ (((False ∨ (p3 ∧ p1)) → p5) ∧ p5)) → (((True ∨ (p3 → p4)) → p2) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
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
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156805338541290441340734300751 : (((True ∨ (p2 ∧ (((p2 ∨ (p2 → p2)) → p4) ∨ (p4 → ((p4 ∨ p2) ∨ (p1 → p2)))))) ∧ p5) ∨ (((p3 ∧ p1) ∨ (p1 ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776069350766190667377716815745 : (((False ∨ (p5 → ((p2 → (False ∨ (((False ∧ p1) ∨ p5) ∧ (p5 ∨ ((p4 ∨ (p1 → p2)) ∧ (p5 ∧ ((p1 → True) ∧ p2))))))) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309852626864595687875337806574 : (p2 ∨ ((((p4 → p3) → p1) → ((p1 ∨ ((p2 ∧ ((p4 ∧ ((p2 ∧ True) ∨ p2)) ∨ p3)) ∧ False)) ∧ p2)) → (((p3 → p3) → p4) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217937913229110677620609314947 : (((True ∧ p5) ∧ (p4 ∧ p4)) → ((((((p4 ∧ p3) ∧ (False ∧ (p2 ∨ p5))) ∧ (p2 ∨ ((p4 ∨ p5) → p5))) ∧ (p3 ∨ p2)) ∧ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719087455419452921631175570700 : ((((False ∧ ((True → True) ∧ False)) ∨ ((p2 ∧ p4) ∨ (((True ∧ (p3 ∨ p5)) → p2) ∧ (p4 ∧ ((False ∧ p3) ∧ ((p4 ∨ p3) → p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64125392988302610793704902971 : ((False ∨ (((p2 → p2) → (p5 ∨ p3)) ∧ (True ∨ (True ∨ ((((p2 ∧ p2) → (p4 → (False ∨ False))) → (True → p1)) ∧ (False → True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206408333540374561640121453637 : ((p3 ∨ ((p4 ∨ p3) → (p1 → p4))) ∨ ((p2 ∨ (p4 ∨ (((True ∨ False) ∧ (p3 ∧ True)) ∨ (p3 ∨ True)))) ∨ (p3 ∧ (False → (p1 → p1))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1807877309084883165191441201 : ((p2 ∧ ((p1 ∨ (True ∧ (p4 → p2))) → (p1 ∧ ((((p2 ∧ p1) ∨ True) ∧ (p2 → (True ∨ True))) ∨ p4)))) ∨ ((True ∨ p4) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59200736358601482887083030039 : (((p1 ∨ p2) ∨ (((p1 ∨ p2) → ((((p1 ∧ p4) ∨ p2) ∨ True) ∧ p1)) ∨ (p4 → ((p2 ∨ ((p2 ∧ True) → p3)) ∨ (False → p1))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38980992749098860579645456420 : ((((p3 ∧ p4) ∧ ((p3 ∨ (p4 ∨ (p2 → ((((p4 ∨ p4) → p4) ∧ (((p2 ∨ False) ∧ False) ∨ (p3 → p2))) → p3)))) ∧ p2)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49574295166126242828275017681 : (((((p1 ∧ ((p5 → ((False ∧ False) → False)) ∨ (p2 ∨ (True ∧ p1)))) ∧ p4) ∨ (p2 ∧ (p4 → (p3 → False)))) → ((True ∧ p2) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774801573307662610150654368295 : (((False ∨ (((((p2 → p2) ∨ p1) → False) ∨ p5) → (p5 ∨ ((p4 ∨ (p1 ∧ (((p5 ∧ p2) ∧ (p2 ∨ (p2 ∨ p5))) → p5))) → p2)))) ∨ p1) ∧ True) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : ((p2 → p2) ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h3
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354734048886575081209432116397 : (p5 → (((((p2 → (p4 → (p2 ∧ (p1 ∨ p2)))) ∨ p3) ∧ (True → (p5 ∧ (p1 ∧ (p2 ∨ False))))) ∨ (p2 ∨ ((p4 → p4) ∨ p5))) ∨ p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47923743640374352109213603553 : ((((((((True ∧ True) → (p2 → (True ∨ (p5 ∨ p5)))) ∧ True) → ((True → p2) ∧ p1)) ∧ True) ∧ ((p5 ∨ True) ∧ p1)) → (p5 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327990621791865017016340001902 : (True → (((p4 → p4) → ((p4 ∧ ((((p1 → (p5 ∧ False)) ∧ ((p1 ∨ False) → p3)) ∨ (True → False)) → p5)) ∧ (p2 ∧ p5))) → (p2 ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p4 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- One of the premise coincides with the conclusion.
  exact h7
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : (p4 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h8
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684354322746684118733437275294 : (((((p2 ∨ ((p2 ∧ ((p4 → p5) ∨ True)) ∧ (p1 ∧ p2))) ∧ ((p5 → p1) ∨ (p2 ∧ p5))) ∨ ((True → p2) ∧ ((p1 ∧ p5) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344456153748621260391951463507 : (p2 → (p5 ∨ (True → ((((p2 ∧ (p2 ∨ ((p5 ∨ False) ∧ p5))) → True) ∨ p3) → ((((p1 ∨ p4) ∨ (True ∨ (p4 ∨ p5))) ∨ False) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113523869390878661019742183219 : (((((p2 → (p3 → True)) ∨ (p4 ∨ (p4 ∨ p1))) ∧ (((p5 → (p2 ∧ ((False ∨ p3) ∧ p2))) → p1) → p5)) ∨ (False → True)) ∨ (p2 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225868702507219924429122527491 : (((False ∧ p4) ∨ p3) ∨ (p1 → ((p1 → p4) → (((p3 → (p4 ∨ (p5 ∨ ((((True ∧ p1) ∨ p5) ∨ p1) ∨ p4)))) → (p4 ∨ p3)) ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116469301552374730256045302540 : (((False ∧ p4) ∧ (True → ((True ∨ ((((p1 ∨ p2) → p1) → ((p3 ∨ False) → p1)) ∧ p2)) → ((p1 ∧ p3) ∧ (p5 ∧ False))))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665293443946460052562445229399 : (((((((p4 → p3) ∨ ((p2 → p4) → False)) ∧ (((p1 ∨ p5) ∨ p4) → ((True ∨ p5) → (p4 ∧ True)))) ∧ p5) ∧ (True ∨ (p2 → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47496481540082511133663279386 : (((p1 ∨ (((True ∨ ((False → p5) ∨ ((True → (p3 ∨ p2)) ∨ ((p1 ∨ p1) ∨ (False ∧ (p2 ∧ p1)))))) → p2) → p5)) ∨ (p2 → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213631035637874142742131078940 : ((((p5 ∧ p1) ∨ p2) ∨ p2) ∨ (((p2 ∨ ((p5 ∧ (((p1 ∨ False) ∨ p5) → p2)) → True)) ∨ (p2 ∨ (p2 ∧ True))) ∨ (p4 → (p3 → True)))) := by
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
theorem thm_5_vars_677160836822341349879611296730 : ((((((p4 ∧ (((True → p3) ∧ (p5 ∨ ((((p2 → p4) → False) → p4) ∨ p4))) ∨ p2)) ∧ False) ∧ p5) ∨ (p3 → (False → (p4 ∨ False)))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_43765920238109270618995327435 : ((((p4 ∧ ((p1 → ((p2 → ((True → p4) ∨ True)) ∨ (p4 ∧ (p3 → ((True → ((p4 → p3) ∧ p5)) ∨ p2))))) ∨ p2)) → False) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698614731464157021207027291300 : (((((p2 ∨ (p2 ∨ True)) ∧ ((p1 ∨ (p3 → (p1 ∨ p5))) ∧ False)) ∨ ((p3 ∨ (False → p5)) ∨ ((True → ((p3 ∨ p4) → p5)) → p5))) ∨ p3) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263801772857919288703077277776 : (True ∧ (((((p4 ∨ p2) ∨ False) ∨ p5) ∨ (((p2 → False) ∨ (True → p2)) ∧ (False → False))) ∨ ((False → (True → p2)) → (p4 → (p3 → p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611470245559804971747906841118 : (((((p3 ∧ (((True → (p5 → (p1 ∨ (((p3 → False) ∧ p1) ∧ False)))) → ((((p2 ∧ p4) → False) → False) → p4)) → True)) → p4) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_301906401207966308132424784136 : (False ∨ ((p2 ∧ p3) → (False ∨ (p5 ∨ (((False ∨ (p3 ∨ (((((p4 ∧ True) ∨ p5) ∧ p5) → p2) ∨ (p2 → p3)))) → (p5 ∧ False)) → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (False ∨ (p3 ∨ (((((p4 ∧ True) ∨ p5) ∧ p5) → p2) ∨ (p2 → p3)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225449126334028038965783422665 : (((p4 ∨ False) ∧ True) ∨ (((p4 ∧ True) ∨ p4) → (((p4 ∧ ((p1 → False) ∨ (p4 → (p1 ∧ p1)))) ∧ (p2 ∧ p4)) ∨ (True ∧ (p5 → p5))))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690238771026636858066267802008 : ((((p5 ∨ (p1 ∨ (((p3 ∨ p4) ∨ (p2 ∨ (p3 → (p4 ∨ p5)))) ∧ (p2 → False)))) ∨ (((False → p3) ∨ (p3 ∨ p5)) ∨ (p5 ∨ p5))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46201298672853403226067600974 : ((((p2 → (p4 ∧ (((p1 → ((p5 → (p4 ∧ p5)) → p4)) ∧ (p1 → p3)) → ((p1 → (p3 ∨ p2)) ∨ p5)))) → p4) ∧ (p4 → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193367109148819941026885591542 : (((p1 ∨ (p4 → p4)) → ((p4 ∨ (p3 ∨ p1)) → False)) → (((((p3 → p5) ∨ p2) ∧ (p3 → False)) ∨ False) ∨ (((p3 ∨ p3) ∧ p4) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63020375013162967851328026296 : ((p4 ∧ (p4 → ((p3 ∨ (p2 → (((True ∨ ((((False ∧ True) ∨ (((p2 ∨ p3) ∧ p1) → p1)) → p3) → False)) ∧ True) → p1))) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158372165599097245390091714129 : (((p4 ∨ p3) ∧ (((False → True) → False) ∧ ((p3 ∨ ((p2 ∧ True) ∨ (p2 ∧ (p2 → p4)))) → p2))) ∨ (False → (p5 ∧ ((p1 → True) ∨ p2)))) := by
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
theorem thm_5_vars_684171412805971865054807224901 : ((((((p5 → False) ∨ ((((p2 ∨ p5) ∨ (p4 ∨ (p3 → True))) → p5) → p4)) ∨ (p5 ∨ p5)) ∨ ((p3 → (p4 → (p2 ∨ True))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256840442468743080093717993674 : ((p1 ∨ p3) → ((p4 → ((((p2 → ((True ∨ p5) ∨ p4)) ∨ p2) → p3) ∨ (p4 ∧ (True → p5)))) ∨ ((((p5 ∨ p1) → p2) → p3) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41785228722073424760440987606 : (((((False → (p5 → p2)) ∨ p4) → ((((False → p3) → False) ∧ (p1 ∧ ((((p4 ∨ p2) → p3) ∨ (p1 ∧ p1)) ∧ p4))) → p5)) ∨ p3) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h10 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : (False → p3) := by
        -- Implications on the right can always be decomposed.
        intro h12
        -- False on the left can always be used.
        apply False.elim h12
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h13 := h3 h11
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h15 : (False → p3) := by
        -- Implications on the right can always be decomposed.
        intro h16
        -- False on the left can always be used.
        apply False.elim h16
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h17 := h3 h15
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h21 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h22 : (False → p3) := by
        -- Implications on the right can always be decomposed.
        intro h23
        -- False on the left can always be used.
        apply False.elim h23
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h24 := h3 h22
      -- False on the left can always be used.
      apply False.elim h24
    case inr h25 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h26 : (False → p3) := by
        -- Implications on the right can always be decomposed.
        intro h27
        -- False on the left can always be used.
        apply False.elim h27
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h28 := h3 h26
      -- False on the left can always be used.
      apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251339285319745879005431935873 : ((p2 → p3) ∨ (p2 ∨ ((p2 ∧ False) ∨ (p1 → ((p4 ∨ (p3 → (False ∨ p1))) ∨ ((p1 → (p1 → p5)) ∨ ((False ∧ (True ∧ p1)) ∧ p3))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620247205376164242457624665580 : (((((p5 ∧ p2) ∨ (True ∧ ((True ∧ (p2 → p2)) ∧ (((((False → (p4 ∧ p4)) ∨ (True → False)) → (True ∧ p5)) → p3) ∧ False)))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57157439384804971639044890123 : ((((False ∧ p3) ∨ False) ∨ ((((p3 → p2) ∧ p3) ∧ ((p1 ∨ p2) ∨ False)) → (((False ∨ (p4 ∨ p5)) ∨ p4) ∨ (False → (p4 ∧ True))))) ∨ p4) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h10
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158415285375441930382311990930 : (((p2 ∧ p3) ∨ (((p1 → p2) → ((p4 ∨ ((p2 ∨ (p1 ∨ (True → p4))) ∧ p4)) ∧ p5)) → p1)) ∨ (((p2 ∧ (p4 ∧ False)) ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221807366797064918874730728317 : (((p2 ∧ p3) → p2) ∧ ((((p1 → (p5 ∨ p5)) ∨ False) ∧ (((((p4 ∧ p2) ∧ ((True ∧ p5) ∨ (p3 ∨ True))) ∧ True) ∧ p2) ∨ p1)) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157510694735917719015810054846 : (((p3 ∧ (False ∨ (p1 ∧ ((((True ∨ p4) ∨ (p4 ∧ p5)) ∧ p2) ∨ (p3 ∧ p2))))) ∨ (p3 ∨ True)) ∨ (p2 → (False ∨ (p5 ∨ (p4 ∨ p4))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148833658076174653034847177378 : ((((p4 ∨ (True ∧ p4)) ∧ p1) ∧ (((False ∧ (False ∧ p1)) ∧ p3) → (p3 ∧ ((p2 ∨ (False ∧ False)) ∧ p1)))) ∨ (p2 ∨ (p5 ∨ (p5 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256356047719152915891672255850 : ((False ∨ p2) → (((((((True ∨ p4) ∨ p5) ∧ p1) → (p4 ∧ (p2 ∨ p1))) ∨ False) ∧ p4) → (((False ∨ True) ∧ (p1 → (True ∧ p5))) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117100891480322341960501715015 : (((p2 → False) → ((((p4 ∧ p4) → True) ∧ ((p2 → ((p3 ∨ p3) ∨ ((p2 ∨ p1) ∧ True))) → ((p4 ∧ p1) ∨ p2))) ∧ p3)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198580736588066029540698488216 : ((p1 ∨ (False ∨ (p1 ∨ ((p1 ∧ p2) ∨ True)))) ∨ (((((p5 ∧ (p2 ∨ p5)) ∧ (p2 → (False ∨ (p3 → (p5 ∨ p5))))) ∨ True) ∧ p2) ∨ p5)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650348378102062228653927334878 : (((((p1 ∨ (p2 ∧ (p3 ∨ ((False → p1) → ((p4 ∧ p1) ∨ (p5 ∨ True)))))) ∧ ((((p4 → p4) ∧ p1) ∧ p5) ∧ p2)) ∧ (p2 → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67627187472956063536745145068 : ((p1 → (p5 ∧ (False ∨ (p2 ∨ ((p4 → p3) ∨ ((((p4 ∧ (((p1 → (False → False)) ∧ p5) ∨ True)) ∧ p1) → p5) → (p5 ∨ p5))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134170679321331699272121974499 : ((((((p2 ∧ (p3 ∨ True)) → p3) ∧ (p4 → (p4 ∨ (p4 ∧ (p2 ∨ False))))) ∨ (p1 ∨ (p2 → (p5 ∨ p4)))) ∨ p2) ∨ (p3 → (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114353493794838261366235406595 : (((p4 → (((p3 ∧ ((p4 ∨ (p5 ∨ p4)) → True)) → ((p3 ∧ (p4 ∧ p5)) ∧ p3)) ∨ p5)) ∧ ((p5 ∧ True) ∨ (p4 ∨ p1))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41198111082083883878711482337 : ((((True ∧ ((((p2 ∨ p5) ∧ ((p1 → p1) ∨ p3)) → (p4 ∨ (p3 → ((p5 ∨ p5) ∨ p3)))) ∧ p3)) → (False ∨ (p1 ∧ p1))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250125621638794092004547268052 : ((True → p4) ∨ (p3 ∨ (False ∨ ((p1 → (((p1 ∧ p4) ∨ ((p5 ∨ p3) ∨ (((False ∨ (True ∨ p4)) ∧ p4) ∧ (p3 → True)))) ∨ True)) ∨ True)))) := by
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
theorem thm_5_vars_61745688254120121067710079536 : ((p1 ∧ (p4 → (((((p5 ∧ False) ∧ (((p2 ∨ ((p3 → p1) ∧ p4)) ∧ p4) → False)) ∨ (p5 ∧ False)) ∨ (p3 ∧ False)) ∧ (False ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55473495611513960124214429142 : ((((p2 → (p2 ∧ p1)) ∧ (p2 ∧ True)) → ((((p4 ∨ True) → p4) ∧ (((False ∨ ((p2 → False) ∨ p1)) ∧ p1) ∧ p1)) ∧ (True ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159316152793609046130168641002 : ((p5 → ((((True → ((p1 → p2) ∨ (False ∨ p3))) ∧ p4) → (p5 → False)) ∨ (p1 ∨ (False → True)))) ∨ (((p3 ∧ False) ∨ (p5 ∨ True)) → p4)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150027922959608466825652965197 : ((p5 ∨ (((p3 → p3) → p5) → (p4 ∨ ((((p4 ∧ True) ∧ (p5 ∨ p5)) → False) ∨ (True ∧ (p4 ∧ p3)))))) ∨ (p2 → (p1 → (p2 ∨ True)))) := by
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
theorem thm_5_vars_621126121337006440059453911159 : (((((p4 → p3) → (p3 → (((((p3 ∧ p4) → True) ∧ (p2 → p3)) ∧ p3) ∧ (p4 → (False ∧ (((p3 ∨ p2) ∧ p1) ∨ p4)))))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58867321698792416617446101204 : (((False ∧ True) ∨ (((((p3 → p1) ∧ (((((True ∧ p3) → p3) ∨ (False → p4)) ∧ p3) ∧ False)) ∨ (False ∧ (p4 → p4))) → p2) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722491464294675134136922775063 : (((((p1 ∨ p3) ∧ p1) ∧ (((p5 ∨ (((p4 ∧ p3) ∧ ((p3 → False) ∨ p5)) ∨ p2)) ∧ False) ∧ (p4 ∧ (False → (p5 ∧ (p3 ∧ True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703144056137211976487106512487 : (((((p1 ∨ p3) → (((p4 ∧ p2) ∧ (p2 ∧ p2)) ∧ p1)) ∨ ((p4 ∧ ((p2 → (False ∧ (p1 → p3))) ∧ (False ∨ p4))) ∨ (p3 → True))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76884130973283037111087043256 : ((((p5 ∧ (p1 ∨ ((True ∨ p2) ∧ (True ∧ (p5 ∨ p1))))) ∨ (((p5 ∧ ((p1 ∧ p2) ∧ True)) → (p2 ∨ (p4 ∧ p5))) ∨ p5)) → False) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∧ (p1 ∨ ((True ∨ p2) ∧ (True ∧ (p5 ∨ p1))))) ∨ (((p5 ∧ ((p1 ∧ p2) ∧ True)) → (p2 ∨ (p4 ∧ p5))) ∨ p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- False on the left can always be used.
  apply False.elim h10



