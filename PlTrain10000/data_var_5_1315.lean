variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168547016510337212151282677355 : ((p1 ∧ (((((p4 ∧ True) → (p4 → (False ∨ p1))) ∧ False) → p4) → (True ∧ (p1 ∨ p1)))) → (p2 → (((p3 ∨ p2) → (p2 ∧ p3)) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : (p3 ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_457362317640693772404271013623 : (((((True → ((p5 ∨ ((True ∨ ((p4 ∨ True) ∧ (p5 ∨ p5))) ∨ p4)) → (p2 ∨ True))) ∨ p4) ∨ ((False → p4) ∨ ((True ∨ False) → False))) ∧ True) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215246155449034664963420535769 : ((False ∧ ((p5 ∨ p5) → p3)) ∨ (((p2 → p1) → ((p2 → (p3 ∨ (((p2 ∨ p5) → p2) → ((p3 → False) ∧ p5)))) ∧ p3)) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39600820031825465020605304860 : (((p2 ∨ ((((p3 → p4) ∧ ((((False ∧ (p3 ∧ p1)) ∨ p4) → (True ∨ (p3 ∨ True))) → (p1 ∧ False))) ∧ p5) ∨ (True → p2))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135915212701317919710834155608 : ((((False → (True ∧ p5)) → ((True ∧ (True ∧ (p3 ∧ p4))) → False)) → ((((True → True) → p3) ∧ (p4 → p5)) ∨ True)) ∨ ((p4 → True) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647509681808944208245338745447 : ((((p5 → (((((p1 ∨ (((True ∧ p2) ∧ ((True ∧ (p1 ∨ p5)) → p4)) → p1)) → p1) → p4) ∧ (p5 ∧ (p5 → p2))) ∧ p3)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789817805647589063147147034445 : (((p5 ∨ ((True ∧ (p3 → False)) ∧ (((p4 ∧ ((False ∨ (p3 → False)) ∧ (p4 ∧ p4))) ∧ (((p4 ∨ p3) ∧ p1) ∨ (p2 → True))) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67415591583712643043140950083 : ((p1 → (((p5 → (((False → p1) → ((p1 → (p4 → p4)) ∧ False)) → (False ∧ p4))) ∨ (((p2 ∨ p3) → p4) ∧ p5)) ∨ (p1 ∨ p5))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249525224060094572276167566040 : ((p5 ∨ p1) ∨ (p5 → ((((((((p5 → p1) ∨ p4) ∨ (p5 ∨ False)) ∨ p1) → p1) ∧ (p3 ∨ p5)) → False) ∨ ((p4 → p5) ∨ (False ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147242228842200970006024779938 : ((((((p3 → p4) ∧ (p3 ∧ (True ∨ (True ∨ (p1 ∧ p1))))) → (p2 ∨ ((p1 → p4) → p1))) ∧ p2) ∨ False) ∨ (((False ∨ False) ∧ p2) → p3)) := by
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
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246143552492053482045968181586 : ((p4 ∧ p2) ∨ (((p4 ∨ (((p3 ∧ (p3 → (((p5 ∨ False) ∧ ((p1 ∨ False) → p2)) → p2))) → p3) → (p2 → p1))) ∨ p4) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37268021642843508918866000473 : ((((p5 ∧ ((((((p4 ∨ p5) → p3) → p3) → ((p3 ∨ p3) → p2)) ∨ p2) ∨ (((p5 ∧ (True ∨ False)) → True) → p1))) ∧ p3) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136239978791465370554094862654 : ((((p5 ∧ p5) → ((p4 → True) → p3)) ∨ (p4 ∨ (False ∨ (p5 ∧ (((False ∨ False) ∨ (p5 ∧ True)) ∧ (p5 → p1)))))) ∨ (True ∨ (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158088981587295948239362305741 : (((p5 ∨ ((p4 → p4) ∨ (p4 → p2))) → ((p1 ∧ (p5 → (p4 → p3))) ∨ ((p2 → p4) → p1))) ∨ (p5 → (p5 ∨ (True ∧ (True → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761813161318096954315788529725 : (((p3 ∧ ((((((p3 ∧ p2) → (p3 → p2)) ∧ ((p5 → (p1 ∧ (p4 ∧ (p3 ∨ False)))) ∧ True)) ∨ (p2 ∧ (True ∧ p3))) ∨ p5) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57075309169162346190818777122 : ((((True ∧ False) ∧ p4) ∨ ((True → ((p2 ∧ ((p1 ∨ p5) → p4)) → ((p5 ∨ (((p3 → p5) ∧ True) → p1)) ∨ (p4 ∨ p2)))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348055146226493573091790229041 : (p3 → ((p2 ∨ False) ∨ ((((p3 ∧ p2) → ((((((p1 ∧ p5) ∧ True) ∨ p2) ∨ (p3 ∧ p1)) → ((p5 ∧ p1) ∨ p3)) ∨ p3)) ∧ p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167219168022071448199851224417 : (((p3 ∨ (((True → (p3 ∧ p5)) ∨ ((p3 ∨ p1) ∨ p3)) ∧ ((p1 ∧ p3) → p4))) ∨ p4) → ((p2 ∧ p3) ∨ (((p3 ∨ p2) ∧ False) → False))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h6
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h16 =>
          -- False on the left can always be used.
          apply False.elim h15
        case inr h17 =>
          -- False on the left can always be used.
          apply False.elim h15
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h21
            -- Conjunctions on the left can always be decomposed.
            let h22 := h21.left
            let h23 := h21.right
            -- Disjunctions on the left can always be decomposed.
            cases h22
            case inl h24 =>
              -- False on the left can always be used.
              apply False.elim h23
            case inr h25 =>
              -- False on the left can always be used.
              apply False.elim h23
          case inr h26 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h27
            -- Conjunctions on the left can always be decomposed.
            let h28 := h27.left
            let h29 := h27.right
            -- Disjunctions on the left can always be decomposed.
            cases h28
            case inl h30 =>
              -- False on the left can always be used.
              apply False.elim h29
            case inr h31 =>
              -- False on the left can always be used.
              apply False.elim h29
        case inr h32 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h33
          -- Conjunctions on the left can always be decomposed.
          let h34 := h33.left
          let h35 := h33.right
          -- Disjunctions on the left can always be decomposed.
          cases h34
          case inl h36 =>
            -- False on the left can always be used.
            apply False.elim h35
          case inr h37 =>
            -- False on the left can always be used.
            apply False.elim h35
  case inr h38 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h39
    -- Conjunctions on the left can always be decomposed.
    let h40 := h39.left
    let h41 := h39.right
    -- Disjunctions on the left can always be decomposed.
    cases h40
    case inl h42 =>
      -- False on the left can always be used.
      apply False.elim h41
    case inr h43 =>
      -- False on the left can always be used.
      apply False.elim h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159021007883750109917965192416 : ((p4 ∨ ((((p4 ∨ (False ∨ p1)) ∧ p4) ∨ p5) ∧ (((p4 → (p3 → False)) → p2) ∨ (p2 ∧ p2)))) ∨ (True ∧ ((False → p2) ∨ (p2 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312252407110468305659099854205 : (p2 ∨ (p1 → ((((p1 ∧ (p4 ∧ p5)) ∨ (p4 ∧ (p3 ∧ p3))) → p5) ∨ ((((True ∨ p1) ∧ True) → p4) ∨ ((p4 ∨ (False → p3)) ∨ True))))) := by
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
theorem thm_5_vars_145759207585362325495179069568 : (((p4 ∧ p5) ∨ ((((p5 ∨ ((p5 ∨ p2) ∧ p1)) → p1) → False) ∨ (True → (True ∧ (p4 → (p5 ∨ True)))))) ∧ (True ∨ (True ∨ (p5 → p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735363038026362129802241272855 : ((((p4 ∨ p1) ∧ ((p5 → ((((True ∧ (p2 → (p4 → (p5 ∨ (p1 ∧ True))))) ∧ ((False ∨ p1) ∨ p5)) → p2) ∧ p2)) ∨ (p4 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41811144844359009600650468460 : (((((True ∨ p2) ∧ False) ∧ (((((p4 → True) → ((p5 ∨ False) ∧ False)) ∨ p4) ∨ ((p3 ∧ p5) ∧ (p2 → (p1 → p5)))) ∧ p2)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_383151942482393065173045080255 : (((((p1 ∨ ((p2 ∧ p1) ∨ (p1 → (p5 ∧ ((((p5 ∨ (False ∨ ((p4 ∨ p2) ∨ True))) ∧ p2) ∧ (p3 → p2)) → p3))))) ∨ True) ∨ p2) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171868243211647639173362625983 : (((p1 ∧ (p3 → (((p4 ∨ p1) → (p1 ∨ (p5 ∧ True))) ∧ (False ∨ p3)))) → p4) ∨ (p4 → ((p4 ∨ ((p5 ∨ p1) → p2)) → (p2 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179881226830680341498123432836 : (((((p3 ∨ (((False → p1) → (p1 ∧ p5)) ∧ p3)) ∨ p4) ∧ p1) ∨ p4) → ((p4 → (p2 ∧ (False → True))) ∨ ((p5 → True) ∨ (p1 → p1)))) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h7
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h15
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250697149585016689324776111103 : ((p1 → False) ∨ ((((p3 → p4) ∧ ((p2 ∧ p2) ∧ (False ∨ (p2 → (True ∧ False))))) ∨ (((False → (p5 ∧ False)) ∧ p1) → True)) ∧ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318533917179821483870503315871 : (p4 ∨ ((p1 → ((((p1 ∨ (False ∨ p2)) ∨ (((p5 ∧ (((p2 → p1) ∨ (p1 → p5)) → p3)) ∨ p4) ∨ p4)) → p2) ∨ p1)) ∧ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65788864564666540034919931716 : ((p4 ∨ ((((p4 ∧ (False ∧ ((p1 ∨ p4) ∨ True))) ∧ p2) ∨ (p1 → p5)) ∨ (p5 ∨ (True ∧ (p1 → (((p5 ∨ p1) → p4) → p4)))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p5 ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347540147782218360008535508901 : (p3 → ((p4 → (((p5 ∧ p4) ∨ p4) ∧ False)) → ((p3 → ((p3 ∨ p5) → False)) ∨ (p2 ∨ ((((False → p2) ∨ (p4 → p5)) → True) ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40160179881905753868547327981 : (((((p2 ∨ ((p5 → p2) ∧ ((True ∨ p2) ∧ (True → p5)))) ∨ (((p1 ∨ (((p3 ∧ False) ∧ p2) ∧ p2)) ∨ True) ∨ p5)) ∧ True) ∨ p1) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_44563384769061971070706585781 : ((((True ∧ ((p1 ∨ p4) → (True ∨ (p3 → p1)))) ∧ (((p1 ∧ False) → p3) → (p2 ∨ (((p2 → p5) ∨ (True ∧ True)) ∨ p2)))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133757707044885365560320626013 : ((((True → ((p1 ∨ p3) ∧ (p2 ∨ False))) ∧ ((((False → p1) ∨ p4) ∧ False) ∧ (((p1 → p2) → p5) ∧ p5))) ∧ p1) ∨ (False → (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66458175687190199845195185706 : ((True → (((False ∨ p1) ∨ (((p1 → p5) ∧ p2) ∧ (p4 ∧ ((((p4 ∧ p1) → p5) ∨ ((p4 ∧ (p1 ∨ p5)) ∧ p5)) → p1)))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617875514779756948165399388769 : (((((((False ∧ p5) → False) → (True → p3)) → ((((p4 → p3) ∧ True) ∨ ((((p4 → p3) ∧ p1) ∨ p3) ∨ False)) → (p1 ∨ p4))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757835412332831520935536146774 : (((p1 ∧ (p2 ∨ ((((((False → True) → p3) ∨ p3) → p5) ∨ (p4 ∧ (p2 ∧ (p4 ∧ p4)))) ∨ (p1 ∨ (((False ∨ True) → False) → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300382750974806585020879110475 : (False ∨ ((((True ∧ (p3 ∨ p5)) → (((True ∧ p4) ∧ p3) ∧ (p5 ∧ p3))) → ((p1 → p2) ∧ ((p4 ∨ False) ∧ p4))) ∨ (p1 ∨ (False → True)))) := by
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
theorem thm_5_vars_664483287453825004272281404489 : ((((p4 ∨ (((p2 ∧ p3) ∨ (p2 → True)) ∧ (((False ∨ True) → (p4 → (((p5 → (p3 ∨ p2)) ∨ True) → p5))) ∨ p4))) → (False ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242585731770726375010803587162 : ((p3 → True) ∧ (True ∧ (((((p5 ∨ p1) ∨ False) ∨ ((p3 → ((p1 → (p5 ∧ p1)) → False)) ∧ (p5 ∧ ((p4 → False) ∨ p2)))) → p4) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153503232986592052304881229656 : ((p5 ∨ ((p2 ∨ False) → ((False → False) ∧ ((p3 ∨ (p4 ∧ (p3 ∧ ((p2 ∨ p2) ∧ (p2 → p4))))) → False)))) → (((p4 → p2) → p1) ∨ True)) := by
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
theorem thm_5_vars_601640467070801702770362166023 : ((((p3 ∧ (p1 ∧ (p4 → ((((False → p3) → (((p4 → p2) ∧ (p3 → p5)) ∨ (True ∧ True))) ∨ ((True → p5) → p3)) ∧ p2)))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41162051916367785490351469249 : ((((p4 ∨ (p3 ∧ ((((p4 ∨ ((((p1 ∧ p4) ∧ p5) ∧ p1) → p4)) ∨ p5) → p2) ∨ (p1 → True)))) ∨ ((p4 → True) ∨ p4)) ∨ p1) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725443286742793388087440299156 : ((((p5 → (p1 ∨ p4)) ∧ (p1 ∨ ((p3 ∨ ((True ∨ True) → ((True ∧ p1) ∨ p3))) ∧ ((((False ∧ (True ∧ p5)) ∧ p2) → p5) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58037899284407709584184456525 : (((True ∧ p5) ∧ ((p1 ∨ p2) → (((((True → p1) ∧ False) ∧ ((False ∧ p5) ∨ ((False → p1) ∨ True))) ∧ (p1 ∨ p4)) ∨ (p5 ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156874550873232570662250880190 : ((((p2 ∨ (((True ∨ ((p5 ∨ p5) ∧ p2)) ∨ ((p3 ∨ p3) → (True ∨ p3))) → p4)) ∧ p1) ∨ p2) ∨ (False → ((False → (False ∧ p4)) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649902005251712691411009804602 : (((((((p4 ∨ (p2 ∨ p5)) → p4) ∨ (True → (((p1 → False) ∨ (p3 ∨ False)) → (p5 ∨ False)))) ∧ (False ∧ (p1 ∨ p4))) ∧ (p3 → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232079591852630252121954379195 : (((p4 ∨ p3) → False) → ((p3 ∧ (p5 → p4)) → ((p2 ∧ p5) ∨ (((p2 → p4) ∧ (p4 ∧ ((p5 ∨ ((p4 ∨ True) ∨ p4)) → True))) → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p4 ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168422743054070039069110605372 : (((p5 ∧ p3) → ((p5 ∧ (p3 ∨ p1)) → ((p1 → p1) ∧ (p3 ∨ (False → (p3 ∧ p4)))))) → (True → (((p1 ∨ (p5 ∨ True)) → p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46057649460637554163422910968 : (((((((True ∧ ((p1 ∧ ((p3 ∨ (False ∨ ((True ∨ p3) ∨ p5))) ∧ (p4 → p4))) ∧ False)) ∧ p2) ∧ p4) ∨ False) ∨ p1) ∧ (True ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109172168149269483336811413618 : ((False ∨ ((((False ∧ (p1 → (((p5 ∧ p3) ∨ (False ∨ (p5 ∨ p4))) ∧ (p4 → p1)))) ∨ (p2 ∧ (p2 → True))) ∧ p4) ∨ True)) ∧ (p5 → True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336356041258585825184477560126 : (p1 → (((p2 ∨ p3) ∨ ((p5 → ((((((p1 → p1) ∨ ((p1 ∨ p4) ∨ False)) ∧ p3) ∧ False) → True) ∧ ((p1 → p2) ∧ p5))) → p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723085919519798320979420091416 : (((((p3 ∨ p4) ∨ False) ∧ (((p2 ∨ (((p2 ∧ p1) ∧ ((p3 → p1) → ((p2 ∨ p1) ∨ ((p5 ∨ False) ∨ p2)))) → False)) → p2) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41127620668997855258337414058 : (((((((False ∨ ((p3 ∧ p4) ∨ ((False ∨ p5) ∨ ((True ∨ p2) ∨ p5)))) ∨ (True ∧ False)) ∧ p3) ∨ p4) ∨ (p2 → (False → False))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727555893967620176530973639899 : ((((p4 ∧ (p2 → p5)) ∨ (((p2 ∨ ((((True → True) ∨ (p5 → p2)) → (True → (p2 ∨ (p2 ∧ p1)))) → (p3 ∧ p4))) ∨ p1) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247883705327796413888931564594 : ((p1 ∨ p2) ∨ (p3 → (((False ∧ p5) ∨ (p2 ∧ (((p4 ∧ p3) → (p5 → p1)) ∨ (False → (((p2 → p1) → p1) → (p4 ∧ p1)))))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342340124545320565595609753060 : (p2 → ((True → ((p3 ∨ ((True ∨ ((True ∧ p2) ∨ ((p5 ∨ True) ∨ p3))) ∨ (p3 ∧ True))) ∧ False)) → (((p2 ∧ p5) ∨ (p4 ∧ p1)) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206120393880026828665491715525 : ((p4 ∧ ((p2 ∧ p1) ∧ (False ∨ p3))) ∨ ((((p5 ∧ (p4 → (((True → p4) → True) → (p2 ∨ p1)))) ∨ (p1 → (p1 ∧ False))) → True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179471247401524738986021206003 : ((True → (((((p5 → ((p5 → p3) ∨ p1)) ∧ p5) ∨ p4) → p1) ∨ p1)) ∨ (False → (((p1 → False) ∧ (p5 → (True ∨ p1))) ∨ (p3 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740679308128707991652173106318 : ((((p2 ∨ p3) ∨ (((p1 ∧ ((((True ∧ (True → p2)) ∨ p3) → (p1 ∨ p5)) → (p5 ∨ p2))) ∧ (p2 ∨ True)) → ((p2 ∧ False) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330288030369223306731838633887 : (True → (False ∨ (p5 → (((p1 ∧ ((((((p4 ∧ p4) → (p5 ∨ p3)) ∨ p3) → p5) ∨ True) → (p4 ∧ True))) ∧ (p4 ∨ p4)) ∨ (p3 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38636892783030119417087741160 : ((((False ∨ (((p1 → False) ∨ p1) ∧ (p4 ∨ p2))) ∨ (((p1 ∨ ((False → p5) ∨ True)) ∧ (True ∧ True)) ∨ ((True ∧ p3) ∧ p3))) ∧ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217829696521211688947279776659 : (((p4 ∨ (False ∧ p3)) → p1) → ((((((p1 → p3) ∧ True) ∧ (p3 ∨ p1)) ∧ False) ∨ p5) → ((((False ∨ p3) ∨ (p3 → p3)) → False) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h13 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h14 : ((False ∨ p3) ∨ (p3 → p3)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h16 := h3 h14
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357282264010375148441957113112 : (p5 → ((p5 ∧ p4) ∨ ((((p3 ∨ (p3 ∧ p1)) ∧ p4) ∨ (p2 → (p1 → (p1 ∧ p2)))) ∨ ((False ∨ (p1 ∧ p2)) ∧ (p4 → (p2 ∧ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340816385457249912638677133409 : (p2 → (((p4 ∨ (((p4 → (p2 ∨ (p5 ∧ False))) ∧ (False ∧ False)) ∨ (True ∧ (p3 ∧ ((True → p1) ∨ (False → p5)))))) ∧ (p2 ∧ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40602756446046095180038557278 : ((((((p3 ∧ ((True ∧ ((False → p2) → ((True ∧ ((p5 ∧ p1) → p5)) → p1))) ∨ (False ∨ (p2 ∧ p2)))) ∨ True) ∨ p4) → p1) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784768434690444963772411604738 : (((p3 ∨ (True → (((((p4 ∨ p4) ∧ (p2 → p4)) → (True ∧ (p2 ∨ p2))) ∨ (((p3 ∨ p3) ∨ p5) → (p3 ∨ p2))) ∧ (p5 → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_427684121033728816306237781054 : (((((((p5 → (p2 ∧ ((p3 → (((True → ((p2 ∧ p2) ∨ p4)) ∧ (p1 → True)) → p1)) → p5))) ∨ p1) → False) ∨ p3) ∨ (p1 → True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309641356044007739746470736518 : (p2 ∨ (((p2 → True) ∧ ((p2 → ((p1 → p3) → (p3 ∧ p1))) ∨ (True ∨ (p1 → ((p5 ∨ True) → (p3 ∨ p2)))))) ∨ ((p1 ∧ p5) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712889739941963480399404350554 : (((((p5 → p4) → (p5 ∧ (p3 ∨ p3))) ∨ (((((((True ∧ p3) ∧ p3) ∨ (p3 → (p4 ∧ False))) ∧ p1) ∧ True) ∧ (p1 → p4)) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694593408193239675507449213956 : ((((p4 ∧ (((p2 ∨ ((p4 ∧ True) → (p4 → (p2 ∨ p4)))) ∧ p5) ∧ True)) ∨ ((p5 → ((p2 → (False ∨ True)) ∧ (p4 ∧ p2))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118161770939503047945458797877 : ((False ∨ ((p3 → (True ∧ p4)) ∨ ((p5 → p1) ∨ (((p5 ∨ (p2 ∨ (p4 ∨ p3))) ∧ True) ∨ ((p1 → (p4 ∨ p2)) ∧ True))))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166283531283160710841701020731 : ((p4 ∧ ((((False → p2) → ((p1 → (p4 → (p5 ∧ False))) → p2)) → (p5 ∧ p4)) → False)) ∨ (p4 → (False → (p5 → (p3 ∧ (True ∧ p2)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670115289148528303617289080489 : ((((((p2 ∨ (True → (p5 ∨ p5))) ∧ False) ∨ (p2 ∨ (((p3 ∧ p2) → (p1 ∧ (p5 ∨ (True ∧ True)))) → p3))) ∨ (p4 → (p4 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120724742872586897824959658465 : ((((p5 → (p1 → (((((((p3 ∨ (p1 → p5)) → False) → (p2 ∧ False)) ∨ True) → p4) ∨ p2) → p5))) ∨ (p2 ∧ True)) ∨ p3) → (p4 ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
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
theorem thm_5_vars_601496378154289887869976947585 : ((((p3 ∧ (((p4 → (p5 ∨ ((p1 ∧ p5) ∧ p4))) ∧ (((p2 ∨ ((p2 ∧ ((p1 ∧ p3) ∨ p1)) ∨ p2)) ∧ p4) → p2)) → p5)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58600524496280916328218038643 : (((False → False) ∧ (p2 ∧ ((p5 → ((((True → p1) → (p4 → p2)) ∨ ((p5 ∧ (False ∧ p5)) → (p3 ∧ (p4 → p2)))) → p3)) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44455867878460993775536475606 : (((((p1 ∧ p2) ∧ ((p1 → ((p4 ∨ p4) ∨ p5)) ∧ (p4 ∧ True))) ∨ ((((p4 ∧ (p1 ∨ p3)) ∨ p3) ∧ (True ∧ True)) ∧ True)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219417417153907976254788084828 : ((p4 ∨ ((p1 ∧ p5) ∧ True)) → ((((p1 ∧ (p5 ∨ (p2 → p4))) → p5) ∧ ((p3 → p4) → (p2 ∨ (False → (False → p5))))) ∨ (False ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186129267309017861144682996665 : ((((True ∨ ((False ∧ p2) ∨ False)) → (False → (True ∨ p3))) ∨ p2) → (((True → (True → (False ∧ p2))) → ((False ∨ (p2 ∨ p5)) ∧ p2)) ∨ True)) := by
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
theorem thm_5_vars_4656559140584156377999886699 : (p5 → (((p4 ∧ (((p2 ∨ False) ∨ p2) ∧ p3)) → p1) → ((p5 ∧ (((p5 ∧ (p3 ∨ p3)) ∨ p5) → ((p3 ∧ p5) ∧ False))) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((p5 ∧ (p3 ∨ p3)) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118326631946175663300827207643 : ((p2 ∨ (((((p1 ∨ (True ∨ (p2 ∨ (((p2 → False) ∧ (p2 ∧ p1)) ∧ p3)))) ∨ p1) ∧ (p2 ∨ (p1 ∨ p5))) → False) ∧ True)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205526514748687672655318903910 : (((False ∨ False) ∧ (p1 ∨ (p1 ∧ p3))) ∨ (((p1 ∨ (p4 ∨ ((False → (((((p3 ∨ False) ∧ p5) ∧ p2) ∧ p5) → p1)) ∧ False))) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208302850545651172089614576799 : (((p4 ∨ p5) ∧ ((p3 → True) → p4)) → (p4 ∨ (False ∧ ((p4 → (((((p4 ∨ ((p1 ∧ False) ∨ True)) ∧ p5) ∨ p4) ∨ p2) ∧ p3)) → p1)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : (p3 → True) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157681750958486771449825231609 : (((p2 ∧ (False ∨ (((((True ∨ p5) ∨ p2) ∧ (p2 ∨ p1)) ∨ p1) ∧ p5))) ∨ (False ∨ (p4 ∨ True))) ∨ (((p1 → p3) ∨ p5) ∧ (False → True))) := by
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
theorem thm_5_vars_171514910084657588746062288868 : (((((p2 ∧ p2) ∧ (((p3 → (p4 → p5)) ∨ (p1 ∧ True)) ∧ p1)) ∧ p3) ∨ p2) ∨ (p1 → (((p2 ∧ True) ∨ (p1 ∨ p3)) ∧ (True ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106534873985320147074701338336 : (((p1 ∧ (((p2 ∧ (p3 ∧ p3)) ∧ p2) ∨ p2)) ∨ (((((False → p3) → True) ∧ p3) ∨ ((True → (p2 ∧ p3)) → p2)) ∨ p5)) ∧ (True ∨ p4)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191204659294341200487629357899 : ((((p2 ∧ p4) → p4) → ((p3 ∧ p1) ∧ (False ∨ p4))) ∨ (True → (((((p2 ∨ p2) ∨ p5) ∧ True) ∧ False) → (True ∧ ((True ∨ p5) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614721156011593604729200537204 : ((((((((p1 → p1) ∨ ((p3 ∨ True) → (p1 ∧ p5))) → ((p2 → p4) ∧ p1)) ∧ (p4 → p2)) ∨ ((p5 ∨ (True ∧ False)) ∨ p3)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48702403563723637673528088233 : ((((((p1 ∨ (p2 ∨ p3)) ∨ p3) → p1) ∨ ((((((p1 → p2) ∨ p1) → p2) ∧ p2) → p5) → (p3 → p1))) ∧ ((False ∧ p5) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199010653999578752581789730289 : (((((p5 ∧ (p4 ∧ p5)) → p2) ∧ p2) ∧ p1) → (((p3 ∨ (p1 ∧ (((p3 → p2) ∨ ((True ∧ p2) → (p3 ∧ p3))) → p3))) ∨ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195269564376871482820354849352 : ((((p3 ∧ (p3 ∨ p1)) ∧ p3) → (True ∨ p5)) ∧ ((((False → (False → p2)) ∧ p2) → (True ∧ p1)) ∨ (((p3 → p3) ∨ (p4 → p4)) ∨ p3))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h8
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116750175020793281559131649498 : (((p5 ∧ p1) ∨ ((p4 ∧ (p5 ∧ (p1 ∧ ((((p5 ∧ (True ∧ (p3 → p4))) ∧ p5) → (True ∧ p2)) → True)))) ∧ (p2 ∧ False))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115762466471360682985780220217 : (((p2 ∨ ((p2 ∧ (p1 ∧ False)) → p5)) → ((p3 ∨ ((((p1 ∧ p5) ∨ (((False ∧ p3) ∧ True) ∨ p1)) → False) → p2)) ∨ True)) ∨ (p4 ∧ p2)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352673392513203833319669633378 : (p4 → ((p1 ∨ p1) ∨ ((((False ∨ ((((p5 ∨ p4) → (False ∨ True)) → p2) ∧ ((p3 ∧ (p3 ∧ p1)) → p4))) → p3) ∨ (p1 → p4)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115051769448422070197296304334 : ((((p1 ∨ (p3 → (p4 → ((p2 ∧ True) ∧ (True ∧ p1))))) → p5) ∨ (False → ((((p1 ∧ False) → (p2 ∨ p2)) ∧ p5) ∨ p2))) ∨ (p1 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214599021278720368241143946395 : (((p4 ∨ p5) ∧ (p5 ∨ False)) ∨ (p1 → ((((p5 → ((p3 ∨ (((False → False) ∧ (p2 ∨ p5)) ∨ True)) ∧ p4)) → False) ∨ (p1 → True)) ∨ p4))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116734594315558569480126730394 : (((p3 ∧ p5) ∨ ((p3 ∨ ((p2 → p5) ∨ ((((False ∧ (False ∧ p3)) → p1) ∧ p4) ∧ (p3 ∨ p1)))) → ((p5 ∧ p1) ∨ False))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68335182706343953257680372004 : ((p3 → ((True → ((p2 ∧ ((True ∧ p5) → (p3 ∧ p4))) ∧ (True ∨ (True → False)))) → (p5 ∧ ((p1 ∨ (p2 ∧ p3)) → (p1 → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205191684052396824809946752454 : (((p5 ∨ (p5 → p4)) ∧ (True → p3)) ∨ (((p5 ∨ True) → p5) → (((True ∨ ((p5 → (p5 ∧ (p3 ∧ p3))) ∨ (True ∨ p4))) ∨ p4) → p5))) := by
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
    cases h3
    case inl h4 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h5 : (p5 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h6 := h1 h5
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h9 : (p5 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h10 := h1 h9
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h13 : (p5 ∨ True) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h14 := h1 h13
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h16 : (p5 ∨ True) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h17 := h1 h16
          -- One of the premise coincides with the conclusion.
          exact h17
  case inr h18 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h19 : (p5 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h20 := h1 h19
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113586628141162766917490937542 : (((p3 ∧ ((p2 ∧ (p3 ∨ (((p2 ∧ ((False ∨ p1) ∨ (p2 → p2))) → p2) → (True ∧ False)))) ∨ (p5 ∨ p3))) ∨ (True ∨ p5)) ∨ (p4 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



