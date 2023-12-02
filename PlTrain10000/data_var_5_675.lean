variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105084952750765947752225477785 : ((((True → (True → (True ∧ (((p4 → ((p2 ∧ (p1 ∨ p4)) → p2)) ∨ (False ∧ p2)) → p3)))) ∧ False) ∨ (p1 → (False → p1))) ∧ (False → p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247483829682387867575919041479 : ((False ∨ p3) ∨ (((True ∧ (p3 → ((p5 ∧ p4) ∧ p1))) ∧ (p5 ∨ (((((False ∨ True) ∧ p3) → p1) ∨ p4) → p2))) ∨ (True ∧ (p3 → True)))) := by
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
theorem thm_5_vars_111915741572818058875261302330 : (((((((p1 ∨ p4) → p1) ∧ (p4 ∨ p4)) → (p1 ∨ (p5 ∧ p2))) ∨ (((p3 ∨ (True ∧ p4)) ∨ False) → (p1 ∧ p2))) ∨ p2) ∨ (p3 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p1 ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (p1 ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351019487276598875194923047267 : (p4 → ((p5 → (((True → ((p1 → False) ∧ (False → (True → ((p4 → (((p1 ∨ True) ∧ p2) ∨ p3)) ∧ False))))) → p3) ∧ True)) ∨ (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314286473504063872649005435712 : (p3 ∨ ((p5 → ((p4 ∧ ((p1 ∨ ((True → (p5 → (False → p5))) ∧ False)) ∧ p3)) ∧ ((True ∨ (False ∨ False)) ∧ p2))) ∨ (p1 ∨ (False → p3)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54192178352181940292091164169 : (((((((p1 ∨ p1) ∨ p5) ∧ True) ∨ False) ∨ True) ∧ ((p5 → ((p1 ∨ p1) ∧ ((p1 → (True ∨ p3)) ∧ (p4 → (p1 ∧ p3))))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346281340743010813795418818023 : (p3 → (((((True → (((p4 → True) ∧ False) ∧ (((p1 ∧ (p2 → False)) → p4) ∧ p1))) ∨ (p2 → (False ∨ p5))) ∨ p1) ∧ p1) ∨ (p5 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351234646648280918227490343757 : (p4 → (((((p3 → (False ∧ (p1 → ((p2 ∨ True) ∧ p3)))) → p2) ∧ True) ∧ ((((True ∨ p1) ∨ p2) → p2) ∧ p3)) ∨ ((True ∨ p4) ∨ p2))) := by
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
theorem thm_5_vars_697176375813691516979489027698 : (((((p2 ∧ (p2 → p4)) ∧ (((p5 ∨ p1) → (p3 ∨ p3)) ∨ True)) ∧ (((((False ∧ (p5 ∧ True)) ∨ p5) ∨ (p1 ∨ p4)) → p3) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337420726242203308308865181378 : (p1 → (((p3 → (p2 ∨ (((p2 ∨ (True → ((p5 ∧ p2) → ((p1 ∧ (p4 ∨ p2)) ∨ p1)))) ∨ p5) ∨ p1))) → False) → ((p5 ∨ p5) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p3 → (p2 ∨ (((p2 ∨ (True → ((p5 ∧ p2) → ((p1 ∧ (p4 ∨ p2)) ∨ p1)))) ∨ p5) ∨ p1))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (p3 → (p2 ∨ (((p2 ∨ (True → ((p5 ∧ p2) → ((p1 ∧ (p4 ∨ p2)) ∨ p1)))) ∨ p5) ∨ p1))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h6
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52759120902582135430133048283 : (((((p2 ∨ ((p4 → (p1 → p3)) → (p2 ∧ p3))) ∨ (p4 → True)) → p3) → (p1 → (p3 ∨ ((((p4 ∧ p4) ∧ False) ∧ p5) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8208293911249929353275148401 : ((((p5 → (((False ∧ (p3 ∧ p2)) ∨ (((p5 ∨ False) → (p3 ∧ (p1 ∧ (False ∨ (p5 ∨ (True ∨ False)))))) ∨ p5)) ∨ p2)) ∨ p1) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68866200907190268121939979517 : ((p4 → (True ∧ ((((((p2 ∨ p2) ∨ p3) ∧ (p4 ∨ False)) ∨ (p4 → p5)) ∨ ((False ∧ p5) ∨ (p4 ∧ p1))) ∨ ((p2 ∨ p1) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67788872790867446824019776977 : ((p2 → (((True → ((((p1 → (False ∨ ((((False ∧ True) ∨ p5) ∧ p3) ∧ False))) ∨ (p5 → (p4 ∧ p2))) ∧ False) ∧ p1)) ∧ p1) → False)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66101863513426657129533605558 : ((p5 ∨ (((p1 → (p4 ∨ ((p4 ∨ ((True → ((p1 → p4) ∨ p3)) ∨ p3)) ∨ (True ∨ p3)))) ∨ ((p3 ∧ False) → (p3 → False))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119854891821254892940340581051 : (((((((p5 ∨ p5) ∨ ((False ∧ (p5 ∨ (((p2 ∨ p1) ∧ (p3 ∧ True)) ∨ p1))) ∨ p2)) ∨ p3) ∧ p4) ∧ (p4 ∨ p1)) ∧ True) → (p2 ∨ p4)) := by
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
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h7
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h7
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- False on the left can always be used.
        apply False.elim h18
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h21 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h22 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h20
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h24
    case inr h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116650637974552495177826126819 : (((p3 → p1) ∧ ((p5 ∨ ((True → (p5 → ((False ∨ p4) ∧ p5))) ∨ (((p5 → p2) ∨ (p3 ∨ (False → False))) ∧ p1))) ∧ False)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698994639598642639067376514016 : ((((False ∨ (((p5 ∨ p3) ∨ (p4 ∧ ((p3 ∧ p4) ∨ p5))) ∧ p4)) ∨ (p3 ∨ (p3 ∨ ((((p5 ∧ p4) ∨ (True ∨ True)) → p1) ∨ True)))) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68374016146272980935673982577 : ((p3 → ((((True → False) ∨ p3) ∧ True) ∧ ((((p5 ∧ (p1 → True)) ∧ (False ∨ p1)) ∧ p5) ∨ (p3 ∨ (p1 ∨ (True ∧ (p1 → False))))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48260708570618462546749809366 : (((p2 ∧ ((True → (False ∨ (p5 ∧ (p4 → False)))) → (((p5 ∧ p3) ∧ (True ∧ (p5 → (p4 → p5)))) → (p2 ∧ p2)))) → (p1 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57074390928704605420272735266 : (((p5 → (p5 → p5)) ∧ (p1 ∨ ((((((((p4 ∨ ((p2 → (p1 → p2)) → p4)) ∧ True) ∧ p5) → False) → p4) → p3) ∨ False) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258779723227909670726717007866 : ((True → False) → ((True ∧ ((p3 ∨ ((True ∨ p3) ∧ (p4 ∨ (p5 → (((p5 ∨ False) → (p4 ∨ p4)) → p1))))) ∧ p5)) ∨ ((False ∧ p2) ∧ p5))) := by
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
theorem thm_5_vars_150361654259507509578001580282 : ((p5 → (p2 ∧ (False ∨ (((((False → ((p5 ∧ True) → p2)) ∨ p1) ∨ True) → ((p3 → p1) → p2)) ∧ True)))) ∨ (((p2 ∧ p3) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113730276662291393003054866545 : (((((((((False ∧ False) ∧ ((p4 → (p4 ∧ p2)) → p3)) → p5) ∨ p4) → True) ∨ True) → (p5 ∨ (p2 → p1))) → (False ∧ p1)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713389260834069590700679517957 : ((((p1 → (((p3 ∨ False) ∧ False) ∧ p4)) ∨ ((p1 ∧ True) ∨ ((p1 ∧ True) ∨ (False → (p1 ∧ (True ∨ (p1 ∨ ((p4 ∨ p1) ∨ p4)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118744034809713324078775688132 : ((p5 ∨ ((((p3 ∧ p2) → (p2 ∨ p3)) ∨ p5) → ((((((p1 → p2) ∨ True) ∧ (True ∨ p2)) ∨ (p5 → False)) ∨ False) ∨ True))) ∨ (p3 ∨ p4)) := by
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
theorem thm_5_vars_1941599835905196548675471682 : (((((((p3 → (p3 → p3)) → p1) ∧ ((((p2 → p1) ∨ p5) ∨ p5) ∧ p3)) ∨ False) → False) ∨ True) ∨ (p4 ∧ ((False ∨ p5) ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204878514266124322056217964490 : ((((p5 ∨ (True ∨ True)) → p3) → p5) ∨ (((p2 → ((((p3 ∧ (p1 → p4)) → p3) ∨ p1) ∧ p5)) ∨ (False → ((False ∧ p2) ∨ p3))) ∨ p2)) := by
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
theorem thm_5_vars_114918696165737129330257843075 : (((((((p1 → (False ∧ p2)) → True) → (p5 ∧ (p1 ∧ False))) → False) → True) → (((p3 ∧ p2) ∧ ((False → p1) ∧ True)) ∧ True)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174476521543950671373667775179 : ((((p1 ∨ (p3 ∧ True)) → (p4 → p4)) ∧ (True → (((p4 → p4) → p1) ∨ False))) → ((((True → p4) → p2) ∨ False) ∨ (p3 ∨ (p5 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (p4 → p4) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66443795563414915111065374558 : ((True → (((((p4 → (p5 ∨ (p3 ∨ (False ∧ ((p1 ∧ (p4 ∨ True)) → p5))))) ∨ ((p3 → True) ∧ p2)) → p4) ∨ (False ∨ p5)) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776591542917055078296915982472 : (((p1 ∨ ((p2 ∧ ((((p1 ∨ ((True ∧ (True ∧ (p5 ∧ True))) → False)) → (p5 ∨ False)) ∧ (False ∨ p3)) ∨ ((p1 → p2) ∧ p1))) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_184273286266674318849547445720 : (((((p3 → (p1 ∨ p5)) → (p3 ∨ False)) → (p2 ∧ False)) → p5) ∨ ((True → True) → ((((True ∨ False) ∧ p5) ∧ p2) → (p5 ∨ (p4 ∨ False))))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718470392354826778397261970299 : (((((p4 ∧ (p1 → True)) → False) ∨ (((p2 ∨ (p2 ∨ ((p4 ∧ (p4 ∧ ((p4 ∧ p5) → p4))) → (p2 ∨ p4)))) ∨ True) ∧ (False → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198304832333639180912160877115 : ((p1 ∧ (((True → p4) ∧ p3) ∨ (True → p3))) ∨ (((False → p2) ∧ (p1 ∧ ((True ∧ (p2 ∧ (((p2 → p2) ∧ True) ∧ p5))) → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702237207750957496702651232232 : (((((((p1 ∧ False) ∨ (True ∨ p3)) → (p1 ∨ p3)) ∧ p5) ∨ (((True ∨ ((False → p2) ∨ p2)) ∧ p5) ∨ ((p3 ∨ False) ∨ (p5 ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606861998074164501548214690257 : ((((((p2 ∨ (p2 → ((False ∧ False) ∨ (((((p5 → (False → p4)) → True) ∨ p4) → True) → p4)))) ∨ ((p3 → p4) ∧ True)) ∧ False) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41423035943548312049808297726 : ((((p2 → (((p5 ∧ (True ∨ (p3 ∨ (p5 ∧ (p1 ∨ p4))))) ∨ p4) ∨ p1)) ∨ (((p2 ∧ (p3 ∧ (True ∨ False))) ∨ p3) → p3)) ∨ p4) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758451442964846648536091055427 : (((p2 ∧ ((True ∧ ((p3 ∨ True) ∧ (((p3 ∨ p5) → False) ∨ (p4 ∨ (True ∨ ((((p4 ∧ (False → p2)) ∧ p5) ∧ False) → False)))))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147040861282242491467493255995 : ((((True → (((p4 → True) ∨ p4) ∧ (p2 ∨ (p1 → (p2 → False))))) ∧ (p4 → ((False ∨ p5) ∨ p1))) ∧ p4) ∨ (((True ∨ True) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40926825143623503999972635856 : ((((((((((p1 → p3) ∨ True) ∨ (((p4 → ((p5 → False) ∧ p3)) ∧ p2) ∧ p1)) → p5) ∧ p3) → p1) ∧ p5) ∨ (False → p3)) ∨ p1) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716409209281143585632066731915 : (((((p1 → False) ∧ (False ∧ p3)) ∧ (((p3 ∨ (((True ∨ ((True ∨ True) ∧ (False → p4))) ∨ (p1 ∧ (p5 ∧ p1))) → p5)) ∨ p3) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191464939832707345883609548528 : (((p5 → p3) → (((p1 ∧ False) → p5) ∧ (p5 ∨ p4))) ∨ (p4 → (p5 ∨ (((((p1 ∧ False) → p2) → p4) → ((p3 → True) → True)) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616415416138211434431153662510 : ((((((((p1 ∨ (((False → False) → p3) ∨ p2)) ∨ True) ∨ p3) → True) → (((p5 → (p3 ∧ (p2 ∨ (True ∧ p2)))) → p1) ∨ p2)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42492073746676662424689279644 : (((False ∨ ((True ∧ (p2 ∧ (((p3 ∨ (p1 ∧ (p4 → False))) ∨ ((False ∨ ((p1 ∨ p2) ∧ p5)) ∧ (p5 ∧ p3))) ∨ p2))) ∨ p5)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191679398677779467308437511053 : ((p5 ∧ ((p1 ∨ p2) ∧ ((p1 ∧ (p2 ∧ p1)) ∧ p2))) ∨ ((((True ∨ True) → ((p3 → (True ∨ p4)) ∨ False)) → (p4 ∨ p4)) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789573120969926760244900648981 : (((p5 ∨ (((False ∧ p1) → ((p1 → (p4 ∨ True)) ∨ False)) ∧ ((((((True → p3) ∨ p1) → p2) ∨ (False ∨ p5)) ∨ p4) ∨ (True ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666642812283304935654648079217 : ((((((p2 ∨ (((False → (True ∨ (False ∨ p2))) → p5) → p3)) ∨ False) → (p1 → ((p2 ∨ (p1 → p3)) → False))) ∧ ((p1 ∧ False) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233673527487209780493260211760 : ((p2 ∨ (True → p3)) → (p2 ∨ (True ∧ ((p2 → p3) ∧ ((True → (((True → p3) ∧ p4) → (p1 ∨ (p2 ∨ (False ∨ p1))))) ∨ (False → p5)))))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774787757676989284665794177996 : (((False ∨ (((p4 ∧ p4) → (p3 ∧ (p1 ∨ p1))) ∨ (((p1 → p3) → (False → p5)) ∧ (((((True → False) → p3) ∧ p4) → p1) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40851029870357270769469818651 : (((((((p5 ∨ False) ∨ ((p4 → (((False ∧ p1) → p4) ∧ p5)) → (False → True))) ∧ (p3 ∧ (False → False))) ∧ p1) ∧ (p3 ∨ p2)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167879681872044372933814774817 : ((((True ∨ True) → (False ∧ ((p2 ∧ False) ∨ (True ∧ True)))) → ((p4 → p4) ∧ (p1 ∨ p3))) → ((p4 ∧ (p1 → ((p4 → False) ∨ p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190602905120391042313543630500 : ((((True ∧ p5) → ((p3 ∧ (p5 ∨ p1)) ∧ p2)) → False) ∨ (((False → (((True ∨ False) ∨ p3) ∨ p3)) ∨ False) ∧ (False → (True ∧ (p1 → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356158345905235013109337832643 : (p5 → ((((True ∨ p4) → (p2 ∧ p5)) ∧ ((((False → p1) → p2) → p4) → ((p3 ∨ p1) ∧ True))) ∨ ((True ∧ ((p3 ∧ True) ∨ p5)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207076974095726862388737212484 : (((p4 ∧ ((p2 → p1) ∧ p1)) ∧ p5) → (((((True → p5) ∧ p5) → ((False ∨ True) → ((p4 ∧ p2) ∧ p1))) ∨ (p2 → (p5 ∨ False))) ∨ p5)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670096719793506177994979956890 : ((((((True ∧ False) ∧ (p5 ∨ (True ∧ p1))) ∧ (((p2 → (False → p2)) ∧ p2) ∧ (p3 ∧ (True ∧ (False → True))))) ∨ (p1 → (p3 → True))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164866912518272079036329804288 : (((p4 ∨ ((p5 ∧ (p3 ∧ (p3 ∧ (((p4 ∧ True) ∧ False) ∨ (p3 ∨ p1))))) ∨ p3)) ∨ False) ∨ (p5 → ((False ∨ p5) ∨ (p2 → (p1 ∨ p3))))) := by
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
theorem thm_5_vars_164534422090312026127574826673 : ((((False ∧ (((p1 ∧ ((False ∨ p1) ∧ p4)) ∧ p3) ∨ False)) ∨ ((p5 → True) ∧ p4)) ∧ p1) ∨ ((p3 ∨ p5) ∨ (((p3 ∧ p1) ∧ p1) → p3))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643324545376335882286171274295 : ((((p3 ∧ (p1 ∨ (((p3 → p2) → (((p4 → ((False ∨ (p1 ∧ p3)) ∧ p4)) ∨ (p5 → True)) ∧ p2)) ∧ ((p4 ∨ p1) → True)))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62342955410903562433478747419 : ((p3 ∧ ((False ∨ ((p1 ∨ ((False ∨ p1) ∨ ((p5 ∨ True) ∧ ((False → p1) ∨ (p3 → False))))) ∨ (True ∨ p5))) ∨ ((p4 → True) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214537442585898871773679108883 : (((True ∨ p1) ∧ (p2 ∨ p5)) ∨ ((p1 ∧ p4) ∨ ((((p2 → True) ∨ (True ∧ p1)) → p4) ∨ (p5 ∨ (((p4 → p4) → (p4 → True)) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157338973947555783952443931140 : (((p2 ∨ ((True ∨ p4) ∧ (((p1 ∧ (True → (False ∨ (p1 ∧ p4)))) ∨ p4) ∨ (p5 ∧ p3)))) → p5) ∨ ((True ∧ True) ∧ (True ∧ (True → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134729977881264606281813082921 : ((((p3 → (p3 ∧ p3)) → ((p2 ∧ (((p4 → p3) ∧ (p5 ∨ p2)) ∨ (((p3 ∧ p5) → p5) → p3))) ∨ False)) → p5) ∨ (p2 → (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_935075169900182720137583005067 : ((((((p2 ∨ (False → p4)) ∨ (False ∨ False)) ∨ p1) → ((p3 → (p2 ∨ (p5 ∨ ((((p2 ∨ True) → p2) ∧ p3) → (p4 → p2))))) ∧ p5)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∨ (False → p4)) ∨ (False ∨ False)) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161035887869649382611878173247 : ((((p4 → True) ∧ True) → (p1 → (p2 ∧ ((p5 ∨ False) → (p3 → ((False ∧ (p1 ∧ p1)) ∨ True)))))) → ((p2 ∨ p4) ∨ (p1 → (p5 ∨ True)))) := by
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
theorem thm_5_vars_612085284690769244949498679901 : ((((((((p3 ∧ ((p1 ∧ True) ∨ p1)) → ((p5 ∨ p4) → (p2 ∨ (p2 → (False → True))))) ∨ p3) → (p5 → p4)) ∧ (True → p2)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_214785752037382260582530258569 : (((False ∨ p5) ∨ (p3 ∧ p4)) ∨ (p3 → ((p2 ∨ True) ∨ ((((p1 ∧ p5) ∨ (True ∨ p1)) ∧ (p5 ∨ p3)) ∨ ((p3 ∧ (p3 → True)) ∧ True))))) := by
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
theorem thm_5_vars_302800692775517448970858893627 : (False ∨ (p5 ∨ (((p4 ∨ (((False ∧ p4) ∨ (((p2 ∨ False) ∧ ((p3 → p2) ∧ (p5 ∧ (True → True)))) ∧ p1)) ∨ p2)) ∨ (p1 → True)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_133818682790400607266125428003 : ((((p1 ∧ p3) ∨ ((p2 → (p1 → (False → (True ∧ (True ∧ ((False ∧ p1) ∧ True)))))) ∧ (False ∨ (False ∧ p1)))) ∧ p3) ∨ ((p5 → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307606895163976929195970185653 : (p1 ∨ (p1 → ((((p3 → p2) → (p2 ∧ ((False → (p3 ∨ p4)) → p4))) ∨ (((p1 → False) → (p3 ∧ p1)) ∨ ((p1 → p4) ∨ False))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232988674506062610317857570928 : ((p3 ∧ (p3 → p5)) → (((p4 ∧ (((False ∨ p4) ∨ False) ∨ (((p3 ∨ p3) ∧ True) ∨ (p4 ∨ True)))) ∧ (p4 → (p1 ∧ p5))) ∨ (True ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786438452239437344007318755244 : (((p4 ∨ ((((p4 ∨ (p4 ∧ (True → p3))) → (p4 ∨ ((p4 ∨ False) ∧ p3))) ∨ p1) → (False ∨ ((p1 ∧ p3) → ((False ∨ p3) ∧ p3))))) ∨ p3) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h9.left
    let h13 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_421814956919473714476557613936 : (((((((((False ∧ True) → p5) ∧ p3) ∨ (((p4 ∧ p3) → (True ∧ ((p5 ∨ p5) ∨ p5))) → (p2 ∨ p5))) ∧ p1) ∨ True) ∧ (p3 ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148468877179506820368526334599 : (((p2 ∧ ((True → False) → ((((p5 ∧ p2) → True) → True) ∧ p3))) ∧ (((False ∨ False) ∨ (p5 → p5)) ∧ p4)) ∨ (p4 ∨ (False → (False ∧ p1)))) := by
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
theorem thm_5_vars_300961659782373657999427585117 : (False ∨ (((False → ((False → p1) ∨ (((p5 ∨ False) ∨ False) ∨ p3))) → p5) ∨ (((((True ∨ p4) → (p1 ∧ p1)) ∧ (p1 ∨ p5)) ∨ True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629255363526415000285356475771 : ((((((((((True → True) ∨ (p3 ∨ p1)) → (p3 ∨ (p2 → ((p3 → p5) ∨ (p4 ∧ (True ∧ p5)))))) → False) ∨ p3) → False) ∨ True) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149155391709575197407786754482 : (((p1 ∨ p5) ∧ ((p2 ∧ p2) ∨ (((p2 ∧ False) ∨ p5) ∧ ((p3 → p4) → (p3 ∨ (p1 → (p4 ∨ p5))))))) ∨ (False → ((p3 → False) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52624333032852514959341639671 : (((((p1 ∧ False) → p3) → ((p3 → p3) ∧ ((p1 ∧ (p3 ∨ p4)) ∨ p1))) ∨ (True ∨ (p3 → (((p4 ∨ (p5 → False)) → p3) ∨ p2)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217630666683910293607067911623 : ((((p2 ∧ True) → p1) → p4) → (((True ∨ p2) → ((p5 ∨ p2) ∧ (p5 ∨ (True ∧ (((True → p2) ∨ (p1 ∨ (False ∨ True))) → True))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_28330078362782316744184806469 : ((True ∧ (((p2 → p5) ∧ ((((p1 ∧ p1) → p4) ∧ (p2 → False)) ∧ p2)) → ((((((p5 ∧ p2) ∨ p4) ∨ p2) → p1) ∨ p4) ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702277708111196278182636318216 : (((((False ∧ ((p5 → p5) ∧ (False ∧ (False ∨ p5)))) ∧ p3) ∨ (p4 → ((p1 → p2) ∧ (((((p1 ∧ p4) ∧ p4) ∧ p2) ∨ True) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38684103164376348549068917768 : ((((p1 ∨ (True → ((p4 → p2) → p4))) ∧ (p2 ∧ ((((True ∨ p3) → ((False ∨ True) → (p5 ∧ (p5 → p1)))) ∨ True) → True))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178643571723223002546422315452 : (((p4 ∨ ((p1 → (p1 ∧ p4)) → False)) → (p5 ∨ (p3 ∧ (p3 → p5)))) ∨ (p2 → ((p3 → ((p2 → False) ∨ ((p4 ∧ p1) ∧ p4))) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730644609546082455506739922388 : ((((p2 ∧ (p3 → p3)) → (((p4 ∨ True) → ((((p3 ∨ (True ∧ True)) → False) ∨ True) ∧ (True ∧ p3))) → (p4 ∧ ((p5 → False) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167959989798102532170855251332 : ((((p1 ∨ (p2 → False)) → (True → (p5 ∧ p4))) → (((p4 → (p3 → p5)) → p2) → True)) → (p4 → (((p5 → p5) → p1) ∨ (p2 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159275307202114050978471142955 : ((p4 → ((((p5 → p1) ∨ p5) ∧ ((p4 ∧ p1) ∨ ((p2 ∨ (p3 ∨ p2)) ∧ p1))) ∧ (p4 ∨ p5))) ∨ ((p4 ∧ p3) ∨ (False → (False → False)))) := by
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
theorem thm_5_vars_612890169884312852864896305679 : (((((False ∨ (((True ∧ (((False → (p2 → p1)) → True) ∧ p1)) → (True → p3)) ∨ (p5 ∨ ((True → p1) → p2)))) ∨ (p3 → p1)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259389175145537928392055514353 : ((False → p3) → ((((p3 ∧ False) ∧ p3) ∨ ((((p1 ∨ (p5 ∨ p5)) ∨ p4) ∧ (p1 ∧ p4)) ∨ (True ∧ p2))) ∨ (p1 ∨ (p3 → (False ∨ True))))) := by
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
theorem thm_5_vars_157360419256151759389143240853 : (((p1 → ((p4 ∧ (p3 ∨ p1)) ∧ (p4 ∨ ((p5 ∧ (p5 ∧ p2)) ∨ ((False → False) ∧ p5))))) → p2) ∨ ((p3 ∨ True) ∨ ((p1 ∨ p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248162872124062058482220029453 : ((p2 ∨ False) ∨ ((p3 ∨ (p1 ∧ (p4 ∨ (p4 ∨ p4)))) ∨ (True ∧ (False → ((True ∧ ((((p5 ∧ p3) → p4) ∧ p2) → (p1 → p1))) ∨ p2))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258912003233325473546943237542 : ((True → p2) → ((p1 ∨ (((p5 → p1) ∧ p5) ∧ p3)) ∨ (p3 → (p5 ∨ (((p1 ∨ (True ∨ p3)) ∧ p2) ∨ (((p4 ∧ p1) ∧ False) ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344898843541714512974206820383 : (p3 → ((((((p4 → (((p2 ∨ ((((p2 → p1) → True) → False) ∧ p5)) ∨ p3) → p5)) → p5) ∧ (p1 ∨ p5)) ∨ (True → True)) ∧ p3) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147489980761455805637325465046 : (((p5 ∧ ((((((p2 → p4) ∨ True) → p1) ∧ p5) ∧ ((p1 → p5) ∨ p5)) ∨ ((p2 ∧ True) ∧ p1))) ∨ True) ∨ ((p1 ∨ (p1 ∧ p5)) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75719851022690677843733677792 : (((((((False → p4) ∧ (p1 ∧ (((True ∧ (p4 → False)) ∨ (p2 → ((p5 ∨ p2) ∨ p3))) → p1))) ∨ True) ∨ (p4 ∧ p4)) ∨ False) → False) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((False → p4) ∧ (p1 ∧ (((True ∧ (p4 → False)) ∨ (p2 → ((p5 ∨ p2) ∨ p3))) → p1))) ∨ True) ∨ (p4 ∧ p4)) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319567586222085921414919066424 : (p4 ∨ ((((((p3 → (p2 → p5)) ∧ p4) → p2) → p4) ∨ p2) → ((p1 ∨ p1) ∨ (((p4 → (p1 → (False → p2))) → (False → p5)) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52463730702657289318394666792 : (((p1 ∨ (((p4 ∧ (p1 ∨ (((p3 ∨ p4) ∨ p2) ∨ p2))) ∨ p1) ∨ p4)) ∧ (p4 → ((((p1 ∧ p1) → p1) ∧ p5) → (p1 ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116361951032492773305944615774 : ((((True ∧ False) → p1) → ((((p5 ∧ ((p2 → p2) → p3)) → (True ∧ (((p3 → p3) ∧ p4) ∧ (p1 ∨ False)))) ∨ True) ∧ True)) ∨ (False ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_340749263171788250142632115899 : (p2 → ((((p5 ∧ ((False ∧ (False ∧ p2)) ∨ p3)) ∧ ((((((p2 ∨ p3) → p2) → p4) ∨ (True → (True ∧ p5))) → p1) → False)) ∨ False) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135428038126599376702656668545 : (((False ∨ (p5 ∧ ((p3 ∧ (p2 ∨ p5)) ∨ (p1 ∧ (p5 ∨ (p1 ∧ ((True → False) ∨ p2))))))) ∨ (p4 → (p2 → p4))) ∨ (True ∧ (p2 ∧ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718530978713589390206919462625 : (((((True → (p1 ∧ True)) → p3) ∨ ((((p2 → p2) ∧ p5) → (p5 ∧ (p5 → (p5 ∧ False)))) ∧ ((p3 ∧ False) ∧ (p3 ∨ (p3 ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



