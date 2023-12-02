variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343048034956398709691165577009 : (p2 → ((p1 ∨ ((True ∨ True) ∨ p4)) → (((False ∧ (p3 ∨ (((True ∨ p3) ∧ p1) ∨ (((p4 → p3) → (p2 → p2)) → False)))) ∨ p2) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67331247926318256257174779048 : ((p1 → (((p2 ∧ (False ∨ (True ∨ (p4 → (((((p5 → p2) ∧ (False → p2)) → p4) → p3) ∧ (p5 ∨ (True ∧ True))))))) → p5) ∨ p1)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344732165550072508886562466562 : (p2 → (p3 → (((p1 ∧ ((p5 → (True ∧ p5)) → (p5 ∨ (p1 → p5)))) ∨ (False ∨ p2)) ∧ (((True → (True → (p5 ∧ False))) → p1) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51152406398635188398399245395 : (((((p3 ∨ False) → (False ∨ ((((False → False) ∨ p3) → p1) ∧ ((False ∨ p3) ∨ p3)))) → p2) ∨ ((False ∨ p1) ∧ (p5 ∧ (p3 ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649111418145606159506869353527 : ((((((p4 → (p2 → ((p5 ∧ False) ∨ ((p5 ∨ p1) ∧ (p2 → p3))))) → (True → (p1 → (False ∨ (p5 ∨ p3))))) → p3) ∧ (p1 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_580615523844053936141830998701 : (((p4 → ((p5 → (((p5 ∧ p5) → ((p5 → p2) → p2)) → ((p4 → p3) ∨ ((True ∧ True) ∨ p5)))) → ((p4 ∧ p2) → (p3 ∨ p4)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188133994219493024164637126718 : ((((p3 ∧ ((p5 ∧ True) ∨ (False ∨ p3))) ∨ p4) ∨ True) ∧ ((p3 → (((p5 → (p2 ∨ (p2 → ((p3 ∨ p2) ∨ False)))) ∨ p5) ∨ False)) ∨ p3)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114249997417559618264692717412 : (((True → (((p5 → (False → ((p1 ∧ p4) ∨ (p1 ∧ (((p1 ∧ p4) → p1) ∧ True))))) ∧ p2) ∧ p4)) → (p4 ∧ (p4 ∨ p1))) ∨ (False ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304065093919472874055796622886 : (p1 ∨ ((p1 ∨ (((True ∨ (p4 → p5)) ∨ p1) → ((p1 ∨ p5) → (p2 ∨ (False → ((((p4 → p1) ∧ p4) ∨ p5) ∧ (p3 ∨ False))))))) ∨ p5)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h6
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h6
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h8
        -- False on the left can always be used.
        apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h10
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h14
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h16
        -- False on the left can always be used.
        apply False.elim h16
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h18
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300969846299346008593400866708 : (False ∨ ((((p1 → p4) ∨ p1) → (p1 ∨ ((p2 → (p1 ∨ p1)) → p2))) ∨ ((p2 ∨ p2) → ((True ∨ ((p4 ∧ (p3 ∧ p5)) ∧ p4)) → True)))) := by
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
theorem thm_5_vars_47839378677002101107039998884 : ((((p2 ∧ (((((((p2 ∨ p4) → False) ∧ (p5 → p4)) ∨ False) ∨ (p4 → True)) ∨ ((p3 → True) ∨ p3)) → True)) → True) → (False ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115649892752756042529149336694 : ((((p2 ∨ ((p2 ∨ False) ∧ True)) → False) ∨ ((p5 ∧ p5) → ((False ∨ (((p3 ∨ p4) → (p5 ∨ False)) ∧ p2)) ∧ (p2 ∨ True)))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311241117926645911631357187233 : (p2 ∨ ((p4 → p2) → ((True ∧ (((p5 ∨ (p5 ∨ p2)) ∨ (p5 ∨ p4)) ∨ (p1 → (((((p5 ∧ False) ∧ True) ∧ p1) ∧ p4) → p4)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630724546076629486747192564000 : (((((p2 → (p2 → (((p2 ∨ ((((p5 ∨ p1) ∨ p3) ∧ False) ∨ ((p3 ∨ p4) ∨ p3))) ∧ (False ∧ p2)) → (p3 → p1)))) ∨ p5) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611710193182273541973675411430 : (((((p5 ∨ ((p1 ∨ (p3 ∨ (True → p3))) ∧ (((((p5 → True) ∨ False) ∧ ((p4 ∧ p5) ∨ True)) → p1) ∧ (p3 ∨ False)))) → False) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264110759322351265067634860486 : (True ∧ ((True ∨ (((p3 ∨ p2) ∨ (p4 ∨ (p4 → p3))) ∨ p4)) → (((p4 ∨ p1) ∨ (True → True)) ∨ ((p2 → ((p3 → p5) ∨ False)) ∨ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h8
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h10
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644943468114736839634286651979 : ((((p2 ∨ (True ∧ ((((((True ∧ False) ∧ p2) ∨ ((p3 → p4) ∧ p1)) ∨ p2) → (((True → (p2 ∧ p4)) → p1) ∧ p1)) ∧ p4))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137093015303288127154620861935 : ((True ∧ ((p2 → ((((p3 ∨ ((p2 ∨ ((p2 ∨ p1) ∧ p2)) ∧ False)) → (p1 → True)) → p3) ∧ (True ∨ p4))) ∨ p3)) ∨ ((p5 ∨ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350367475714735546307066859617 : (p4 → (((((((((((p4 ∨ (False ∧ True)) → (p4 ∨ p2)) ∨ (False → p1)) ∨ False) ∧ (p3 ∨ p2)) → False) ∨ p2) ∨ True) → p3) ∧ p1) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((((((((p4 ∨ (False ∧ True)) → (p4 ∨ p2)) ∨ (False → p1)) ∨ False) ∧ (p3 ∨ p2)) → False) ∨ p2) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_887800105350156480281740787693 : (((((p4 → ((p3 → False) ∨ ((p1 ∨ (p2 → (p2 → (False ∨ (p1 ∧ (p3 → p1)))))) ∨ (True ∨ True)))) ∨ (True ∧ p2)) → (p1 ∨ p1)) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 → ((p3 → False) ∨ ((p1 ∨ (p2 → (p2 → (False ∨ (p1 ∧ (p3 → p1)))))) ∨ (True ∨ True)))) ∨ (True ∧ p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683886665688351415336911057788 : (((((p4 ∨ (((p3 ∨ False) → ((True ∨ (p3 ∨ (p3 → p5))) ∧ p4)) → (p4 ∨ p5))) ∨ p4) ∨ ((p2 ∧ False) → ((False ∧ p4) ∨ p1))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46157989442905066268478116831 : (((((((p4 ∨ (p2 → True)) ∨ (True ∧ ((((p2 ∧ p1) ∧ p4) → p3) ∧ False))) ∧ p1) → ((False → p1) ∨ False)) → p2) ∧ (False ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53744383116314196842011232536 : ((((((((p2 ∨ p1) → p4) ∧ p1) → p4) ∧ p5) ∧ p5) ∨ ((((False ∨ p5) ∧ ((p2 ∨ ((True ∨ True) ∨ p4)) → p4)) ∨ p3) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250881432056180530798584232436 : ((p1 → p3) ∨ ((p4 ∧ (((p2 ∨ ((p4 ∧ p2) ∧ (False ∨ (((p4 ∧ p5) ∧ p4) ∨ p5)))) → p5) ∧ (p2 ∨ (False ∧ False)))) ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732077879833178058237811785528 : ((((True ∧ p1) ∧ (p3 ∨ ((p5 ∨ (((p1 ∧ p1) → ((p5 → ((p1 ∧ p1) → (False ∧ True))) → p4)) ∧ p2)) ∨ ((p2 ∧ False) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255084788638796183169775828723 : ((p4 ∧ p2) → (((p1 ∧ ((p5 → p4) ∧ (p3 ∧ False))) → p3) → (False ∨ (((False ∨ (p4 → (True → p1))) ∨ p4) ∨ ((p4 ∧ p5) ∧ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58984658557486086234636537151 : (((p3 ∧ True) ∨ ((p5 ∧ ((p4 ∧ (p4 → ((p4 → ((False → ((p2 ∧ True) ∨ ((p1 → p5) ∧ p2))) ∨ p3)) → p5))) ∧ p3)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140745474884198488098787826386 : ((((p5 ∨ (True → ((p5 ∧ (p3 ∧ p3)) ∨ p2))) ∨ ((p5 ∧ p4) ∧ True)) → ((p3 ∨ ((True ∨ p3) → p2)) ∨ p4)) → ((p4 → p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116493816637291581920223174131 : (((p3 ∧ True) ∧ ((p5 → (p1 ∨ (p2 ∧ (((p3 ∨ False) ∨ p1) ∧ p5)))) ∧ (p4 → ((True ∧ ((p1 ∧ p1) ∧ p1)) → p2)))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607348527709848798285183851723 : ((((((p2 → (True ∧ p2)) → ((p5 ∧ ((((p5 ∨ p1) → ((False ∨ p4) ∨ False)) ∧ p4) ∨ ((False ∨ p2) → False))) ∨ p1)) ∧ True) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234045666523246890148544330305 : ((p5 ∨ (p2 → p5)) → (((False ∨ (((((True ∧ (p2 → p2)) ∨ ((p1 → p2) ∧ (p4 ∧ p3))) → p5) ∨ p2) → p4)) ∨ (p2 → True)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137856982357945523676597095306 : ((p3 ∨ (False ∧ (((((p1 → False) ∨ True) ∧ (p2 ∨ p4)) ∨ ((False ∨ True) ∧ p2)) ∧ (p5 ∨ ((p3 ∨ True) ∧ p1))))) ∨ ((p5 ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684342827504852346454932099953 : ((((((((p4 ∨ p2) ∧ (p5 → p5)) ∨ p1) ∨ (False ∨ p3)) ∧ (p5 ∨ (p2 ∧ (p5 → p1)))) ∨ (True ∧ ((True ∧ (p1 ∧ False)) → p4))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206131597551873754760485210746 : ((p4 ∧ (p1 ∧ (p5 ∧ (p2 ∧ p2)))) ∨ (p4 ∨ (((p4 → ((p3 ∨ p5) ∨ (True ∧ True))) ∧ (p4 ∧ False)) → (False → ((p1 ∧ p2) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44464932802192618898582358406 : ((((((p3 ∧ (p5 → ((True ∨ p3) → (p4 → p2)))) → p5) ∧ p5) → (((p4 ∨ p2) ∧ (p1 → (p5 ∧ (p4 ∨ False)))) ∧ True)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59952644093236850292555134476 : (((True ∨ p3) → (((((True → p2) ∨ (((p2 → ((p2 ∧ p1) ∧ (p3 ∧ (p5 ∧ p5)))) → p2) ∧ p4)) ∨ p2) → (False ∨ False)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37601063092472216285298331933 : (((((((p2 → p3) ∨ (False → (p2 ∨ ((p4 ∧ p5) → ((False ∨ (p1 ∨ p5)) ∧ (p4 ∧ (p2 ∧ False))))))) ∨ p1) ∧ p1) → p3) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114886956880257584961502145620 : (((p2 ∧ (((p3 ∧ p5) → False) ∧ (False ∨ ((p2 ∨ p2) ∧ (p3 → p3))))) ∨ ((True → False) ∧ (((False ∧ p2) → True) ∧ p1))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318582834356902204137247550834 : (p4 ∨ (((((True ∨ p2) → p3) → ((p4 ∧ ((True ∨ p4) ∧ p1)) → ((p1 ∨ ((p4 ∨ p3) ∧ p4)) → p3))) → (False ∧ p1)) ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700817762276068360157616970336 : (((((p4 ∧ (p1 ∧ ((p5 → p1) ∧ (False ∧ p4)))) ∧ p1) ∧ ((p4 → p4) ∨ ((p5 ∨ ((p1 → (p5 → True)) ∨ p2)) ∧ (p5 ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114511123272526186480857021246 : ((((p4 ∧ p3) ∨ ((p2 → ((p2 → p1) ∨ (p4 ∧ (False ∧ p2)))) → ((p3 ∨ p1) ∨ p4))) → (((p5 ∨ p4) ∧ p1) ∧ p3)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60949960665725955707896759831 : ((False ∧ ((((p3 ∧ ((((p1 → True) → (False ∨ p3)) ∨ p2) ∧ p3)) → (True → (((p3 ∧ (p2 → p1)) → False) ∧ p2))) ∨ False) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713784513270512325871534987206 : ((((((p2 ∨ (p4 ∨ True)) ∧ p2) ∨ False) → ((p3 ∧ True) ∨ (p3 ∨ ((p3 ∨ p4) → ((p4 ∧ (False ∧ p4)) → (p1 → (p2 → p3))))))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h7.left
      let h11 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Implications on the right can always be decomposed.
        intro h17
        -- Implications on the right can always be decomposed.
        intro h18
        -- Implications on the right can always be decomposed.
        intro h19
        -- Conjunctions on the left can always be decomposed.
        let h20 := h17.left
        let h21 := h17.right
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- False on the left can always be used.
        apply False.elim h22
      case inr h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h25
        -- Implications on the right can always be decomposed.
        intro h26
        -- Implications on the right can always be decomposed.
        intro h27
        -- Implications on the right can always be decomposed.
        intro h28
        -- Conjunctions on the left can always be decomposed.
        let h29 := h26.left
        let h30 := h26.right
        -- Conjunctions on the left can always be decomposed.
        let h31 := h30.left
        let h32 := h30.right
        -- False on the left can always be used.
        apply False.elim h31
  case inr h33 =>
    -- False on the left can always be used.
    apply False.elim h33
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769165711973876737355873505244 : (((p5 ∧ ((p4 → True) ∧ (((p2 → p3) ∨ (((False ∨ p4) → p2) ∨ p4)) ∨ (p3 ∨ ((True ∧ p3) → (((p1 ∧ p3) ∨ True) → p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161546104325636069570157811205 : ((p5 ∧ ((True → (p5 → (True ∨ False))) ∨ ((p2 ∨ (False → ((p3 ∧ p3) → p4))) ∧ (True ∨ True)))) → ((p1 ∨ (p5 → (p4 ∨ p3))) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
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
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336114468777175309136530279820 : (p1 → (((((p2 ∨ (p5 ∧ p3)) ∨ ((p3 ∧ p3) ∨ ((((True → p2) → p4) → ((p4 ∨ (p4 ∨ True)) ∧ False)) → p3))) → False) ∨ True) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142844476946098728999716000546 : ((p4 ∨ (((p2 → p4) ∨ ((True ∨ p5) ∧ (p4 ∨ ((False ∨ ((p5 ∨ True) → (p1 ∨ p1))) ∨ (False ∧ False))))) ∨ p3)) → ((p4 ∨ False) ∨ True)) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h10 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h11 =>
            -- Disjunctions on the left can always be decomposed.
            cases h11
            case inl h12 =>
              -- Disjunctions on the left can always be decomposed.
              cases h12
              case inl h13 =>
                -- False on the left can always be used.
                apply False.elim h13
              case inr h14 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
            case inr h15 =>
              -- Conjunctions on the left can always be decomposed.
              let h16 := h15.left
              let h17 := h15.right
              -- False on the left can always be used.
              apply False.elim h16
        case inr h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h20 =>
            -- Disjunctions on the left can always be decomposed.
            cases h20
            case inl h21 =>
              -- Disjunctions on the left can always be decomposed.
              cases h21
              case inl h22 =>
                -- False on the left can always be used.
                apply False.elim h22
              case inr h23 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
            case inr h24 =>
              -- Conjunctions on the left can always be decomposed.
              let h25 := h24.left
              let h26 := h24.right
              -- False on the left can always be used.
              apply False.elim h25
    case inr h27 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720236646961373817719245583404 : (((((p2 → (p1 → p3)) ∧ p1) → (p4 ∨ ((False ∨ ((((p5 → p3) ∨ (p4 ∧ ((p5 ∧ False) ∧ (p5 ∨ p1)))) ∧ p3) ∨ p4)) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183990445105569879694126933458 : (((((False ∨ p2) ∧ ((True ∧ (True → True)) ∧ p3)) ∧ p2) ∨ p1) ∨ (True → (((p5 → (False ∨ (p3 ∨ False))) → p3) ∨ (True ∨ (p3 ∨ True))))) := by
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
theorem thm_5_vars_350272357591729674670245380354 : (p4 → ((p4 ∧ (((((p5 ∧ p3) → p1) ∧ p1) → (p2 ∨ (((p5 ∧ p4) ∨ p4) → p1))) → (p4 → (p3 ∨ ((False ∧ True) ∧ p2))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230239854739734548502398892627 : (((True ∨ p5) ∧ True) → ((((((p2 → True) ∨ p5) → p3) ∨ (p4 ∧ (p5 → (True ∨ False)))) ∧ (p5 → p2)) ∨ (((False → p1) ∨ p4) ∨ p3))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135628462107788670427962386387 : ((((False → (True ∧ (((p1 → p1) ∧ ((p3 ∨ p4) → p2)) ∧ (p1 ∨ p2)))) ∧ p2) → (((p4 → p3) ∨ p1) ∨ p3)) ∨ (False → (p2 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65339515085412538240655090622 : ((p3 ∨ (((((p2 → ((False → (p1 → p3)) ∧ p5)) ∨ p3) → ((p4 → True) ∧ p4)) ∧ True) ∧ ((p2 → ((p4 ∨ p3) → p4)) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732608918652972578982341140662 : ((((p1 ∧ p1) ∧ (((p1 ∧ ((p1 ∨ (False → (False ∨ (True → (p5 ∨ p5))))) → (p1 ∧ (p5 → p2)))) → p4) ∧ (p3 ∨ (p1 ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258765385706259206042043144514 : ((True → False) → (((p5 ∨ ((p3 ∧ (True ∧ p2)) ∨ p5)) → ((p3 → (p1 ∨ ((p4 → p4) ∨ p4))) → ((True ∧ p1) ∧ (p3 ∨ p4)))) ∨ p4)) := by
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
theorem thm_5_vars_158717374990016119165535128584 : ((p3 ∧ (((True → ((p4 ∧ (False ∧ False)) ∧ (False → (p5 ∨ False)))) ∨ p2) ∧ ((p3 ∧ p5) → False))) ∨ ((p2 ∨ (p1 ∨ True)) ∨ (p5 ∨ p3))) := by
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
theorem thm_5_vars_147827306016457022694967507578 : (((False ∨ ((p4 → p4) → (((((p5 ∧ ((False ∨ p4) ∧ p5)) ∨ (False ∧ True)) ∧ p5) ∨ p3) → p5))) → False) ∨ (True ∨ ((p3 ∨ p3) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166420868685400625578264140315 : ((p1 ∨ ((p2 → (p4 ∧ (p2 ∨ (True ∨ (p2 → p3))))) ∨ ((p4 → p5) → (False ∧ False)))) ∨ ((p5 ∧ (((p5 ∧ False) ∨ p3) ∧ p2)) → p2)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68089678447081747125840631259 : ((p2 → (p5 ∨ ((p3 ∧ ((p3 → (p4 ∧ (p5 → ((False ∧ False) ∧ p5)))) ∧ p4)) → ((p3 → p1) ∨ ((p2 ∧ (p2 ∨ p4)) ∨ True))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740570098373525481471692355003 : ((((p2 ∨ False) ∨ ((p2 ∧ (p5 ∧ False)) ∨ ((p2 ∨ ((((p5 → p3) → p2) ∧ (False → p1)) ∧ p4)) ∨ (False → (True ∨ (p3 ∧ p4)))))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55376777025767390208951501462 : (((((p3 → (p5 ∧ p5)) ∨ p3) ∧ p2) → (p5 → (((p1 ∨ (p1 → (p1 → (False ∨ (((p4 → p4) → p4) ∨ True))))) ∧ p1) ∨ p2))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603728472597822834531137200367 : ((((p4 ∨ (((p4 → ((((p1 ∨ p2) ∧ (((((p4 → p5) ∨ False) → p5) → True) ∧ p2)) ∨ p2) ∨ p2)) ∨ p5) → (p5 → p4))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336187796810825015799447768879 : (p1 → ((((((p1 → ((p2 → False) ∨ True)) ∨ ((p3 ∧ (p5 ∨ False)) ∨ (False → p2))) → False) ∨ ((p4 ∨ True) → True)) ∧ (p5 ∨ True)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193831169064440934525337891618 : ((p5 ∧ (p4 ∨ (((False → p5) ∨ (p5 ∧ False)) ∧ p1))) → ((p3 ∨ (((p2 → p5) ∧ (False ∨ p1)) ∧ True)) → ((p4 ∨ (p1 → p4)) ∨ p5))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- False on the left can always be used.
        apply False.elim h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h1.left
      let h22 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h27 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h28 =>
          -- Conjunctions on the left can always be decomposed.
          let h29 := h28.left
          let h30 := h28.right
          -- False on the left can always be used.
          apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683482241025247308063843120620 : ((((p3 → ((((p4 ∨ p4) → (True ∨ (True ∨ ((p1 → p5) ∨ p4)))) → (p3 ∧ p1)) ∨ True)) ∧ (((p1 ∧ True) → p2) ∨ (p5 ∨ True))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729969075800671661147755209879 : (((((p5 ∧ p1) → p4) → ((p3 → (((p3 → p4) ∧ False) ∧ (((p2 ∧ p2) → (p5 ∧ (p3 ∨ p1))) ∨ ((p1 ∨ p2) → p4)))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51085448045926636150179259574 : ((((((True ∨ (((p3 ∨ p2) ∨ (p1 ∨ p1)) → True)) ∧ (p1 → (p5 → p2))) ∧ p2) ∧ p1) ∨ ((p2 ∧ (p3 ∨ p5)) ∨ (False ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684939335370871151682928982046 : ((((p2 ∧ (((((p5 ∨ (p5 ∨ False)) ∧ p5) ∨ p3) ∨ (p3 → (p1 ∧ False))) ∧ (False → p2))) ∨ (True ∨ (p1 ∧ (p4 ∧ (p1 ∨ True))))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_192947441563591817864855713739 : ((((p2 ∧ p5) ∨ ((False → p2) → p3)) ∨ (p2 → p4)) → (((p5 ∨ p5) ∨ (((False → (p5 ∨ (False → False))) ∨ p4) ∧ (True ∧ False))) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
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
theorem thm_5_vars_225919327919738574409849557924 : (((p2 ∧ True) ∨ p3) ∨ (p3 → ((p5 ∧ ((((p1 → True) → (False ∨ (p3 ∨ p5))) → p2) ∧ (p4 ∨ (True → (p2 ∧ p1))))) ∨ (p1 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158711387791650282205144132316 : ((p3 ∧ ((((p5 ∧ p5) ∧ (p2 ∧ (p5 ∧ (p1 ∧ (True ∧ (p2 → (p5 ∨ True))))))) → True) → False)) ∨ ((p1 → (p4 ∨ (True ∨ False))) ∨ p4)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134632702032003056388280879921 : (((((((False ∨ p5) ∧ ((p3 ∨ p2) ∧ p3)) ∧ (p3 ∨ p1)) ∨ (p4 ∧ p2)) ∨ ((p4 → (False → p2)) → True)) → p4) ∨ (False → (p4 ∧ p3))) := by
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
theorem thm_5_vars_231460625387658532462971426969 : (((p2 → p5) ∨ False) → ((((p5 ∨ False) ∨ (((False ∧ p5) ∧ ((p5 ∨ p4) ∨ p5)) ∨ (p3 ∧ (p3 ∨ (p4 → (p2 ∨ True)))))) ∨ p3) ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123875858453913348616488344842 : ((((p1 ∧ p2) → ((True → (p1 → (False → p1))) ∨ ((p4 ∧ True) ∧ p4))) → (((((p1 → p3) ∨ p4) ∧ p2) ∧ p1) ∧ p1)) → (p2 ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∧ p2) → ((True → (p1 → (False → p1))) ∨ ((p4 ∧ True) ∧ p4))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_432190073908880176495492433883 : ((((p4 ∨ (p1 ∨ (p1 ∨ (p5 ∨ (((p3 ∧ True) → (p2 ∧ (False → p1))) → (((p1 ∨ p4) ∨ p3) → (p5 ∨ p4))))))) ∨ (p3 ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697518175527946602001046401037 : ((((p5 ∧ (((((p3 ∧ p2) ∨ p5) ∧ (True ∨ p2)) ∨ False) ∧ False)) ∧ (False → ((p1 → (((p5 ∨ (True ∨ p4)) ∧ p4) ∨ p5)) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133998812629928782985920365985 : (((((p2 ∨ (True → p1)) ∧ ((((False ∨ True) ∧ (True ∧ (p1 → ((True → p1) ∧ p1)))) ∧ False) ∧ p4)) ∧ p3) ∨ p2) ∨ ((True → False) → p5)) := by
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
theorem thm_5_vars_40456255066776218366175510040 : (((((((True ∧ True) → True) → p5) ∨ ((p4 → ((p3 → ((True ∨ False) → p3)) → (p3 ∧ (True ∧ (p4 → p3))))) ∨ p2)) ∨ p4) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49887640732180456755985305934 : (((((p2 → ((p3 → p4) → (p5 ∧ (p2 ∧ p5)))) ∧ ((((p5 ∨ False) ∧ p2) ∨ False) ∧ p5)) ∨ p4) ∧ (p2 ∨ (p4 → (p5 ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623571303601495108996423666127 : ((((False ∨ (p1 ∧ ((p4 ∨ (((p3 ∧ p2) ∨ p2) ∨ p4)) ∨ ((((p5 → True) → p2) ∧ ((False ∧ True) → (True ∨ p3))) → p3)))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_172418341365117420050914650200 : ((((True → (p3 → p2)) → p5) ∧ ((True → (True ∨ ((p1 → p3) → p1))) ∨ p1)) ∨ ((p4 ∨ (p3 ∨ ((True → p1) ∧ (p1 → p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52411562566353944013860824939 : ((((True ∨ (False → False)) ∨ (((((p4 ∨ False) → True) ∧ p4) ∨ p2) ∨ p5)) ∧ (((False → p4) → (p1 ∧ p5)) ∨ (p4 → (p3 ∨ p4)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149245959548640920980447338012 : (((p1 ∨ p1) ∨ ((((((p3 ∧ p4) → p1) ∨ p1) ∧ (p2 ∨ (p2 → p4))) → (False ∧ (p1 → p4))) ∨ p4)) ∨ (True ∧ ((p4 ∧ False) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149945051108862560015729715952 : ((p3 ∨ (p1 ∨ (p1 → (((p4 ∧ ((p4 ∨ True) ∨ ((((p1 ∧ p1) ∧ p1) ∨ p1) ∧ p5))) → p5) ∧ False)))) ∨ (((p2 ∨ False) → p2) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51218638744979227778835219210 : (((((False → (p2 → (False ∨ p1))) ∧ p2) ∨ ((((False ∨ p2) ∨ (False ∨ p3)) ∧ p2) ∧ p3)) ∨ (((p4 → p5) ∧ (p4 ∧ False)) → p1)) ∨ p2) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330404314355510240641646014408 : (True → (p2 ∨ (p5 ∨ (p3 ∨ ((((((p4 ∨ False) ∧ False) ∧ p5) → p2) ∧ ((p4 ∨ p1) ∧ ((True → p5) → True))) ∨ ((False → p2) ∨ p5)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119401079983968268522066376395 : ((p4 → ((((((False ∧ p5) ∨ ((p1 ∨ ((False ∨ False) ∧ ((False ∨ p1) → p5))) ∧ True)) ∨ p2) ∧ True) ∧ (True ∧ p3)) ∨ True)) ∨ (p5 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712757522676376893246031914483 : (((((p1 ∨ p5) ∨ (p4 ∨ (p2 ∨ p3))) ∨ ((p2 ∧ ((p2 ∨ p3) ∧ (p5 ∨ True))) ∨ ((p3 → (False → False)) ∧ ((True ∨ p2) ∨ p2)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187162316761838029416329590429 : (((p4 → p3) ∨ (p3 ∨ ((p4 → p5) ∧ ((p2 → p3) → True)))) → ((p5 ∧ p2) ∨ (((p4 ∧ ((p3 ∨ p5) → (p3 ∧ False))) ∧ p3) → True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138338384386567149265167902026 : ((p4 → (((False ∨ ((p2 ∧ (p3 → ((p2 ∨ p5) ∨ p1))) ∨ ((False → ((p2 ∨ False) ∨ p2)) ∨ p4))) ∨ p4) ∧ p5)) ∨ ((p5 → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135773025520212470391890576451 : ((((((((True ∧ p1) ∨ True) → p2) ∧ p2) ∧ ((False ∨ True) → p4)) ∨ p4) → ((((p3 ∧ p4) ∧ False) ∧ p4) ∨ True)) ∨ (p4 ∧ (p2 ∨ False))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
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
theorem thm_5_vars_316438900769570947795498732216 : (p3 ∨ (p1 ∨ (((True ∨ p2) ∧ (True ∧ ((p1 ∧ True) → ((p3 ∨ p3) → ((p5 ∨ (True → (p4 ∧ False))) → (p5 ∧ True)))))) ∨ (p2 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h1.left
      let h7 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h1.left
      let h10 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h1.left
      let h14 := h1.right
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h16 := h11 h15
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h1.left
      let h20 := h1.right
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h21 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h22 := h11 h21
      -- We need to get the right conjuct of h22 based on <expert-advice>.
      let h23 := h22.right
      -- False on the left can always be used.
      apply False.elim h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356327824153129356811686103565 : (p5 → (((p4 → (p1 ∧ True)) ∨ ((p3 → (p3 ∧ (True ∧ False))) → (p2 ∨ p5))) ∧ (p3 ∨ ((((False ∧ p3) ∨ (False → p1)) → p3) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∧ p3) ∨ (False → p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809751113881933263161990850345 : (((p5 → (((((p1 → ((p4 ∨ (p4 → ((False ∧ p3) ∨ p3))) ∧ (True ∨ (p2 → p3)))) ∧ (True → p5)) → p4) ∨ p2) ∨ (p1 → True))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_234052402802320306040880932639 : ((p5 ∨ (p4 → True)) → ((p5 ∧ ((p3 ∧ False) ∨ ((True ∧ (p2 ∨ p5)) → p4))) → ((True ∧ ((p1 → p4) ∧ (p4 ∨ (p3 ∨ p5)))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
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
    cases h1
    case inl h9 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h10 : (True ∧ (p2 ∨ p5)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h11 := h8 h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h11
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h13 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h14 : (True ∧ (p2 ∨ p5)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h15 := h8 h14
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h16
      -- One of the premise coincides with the conclusion.
      exact h15
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136349169314705026792716528322 : (((True → ((p1 ∨ p3) → True)) ∧ ((p1 ∧ p5) ∨ ((p2 ∨ (((p3 ∧ p3) ∧ (p5 ∧ (False ∨ p5))) ∧ p1)) ∨ p2))) ∨ (False → (True ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609434189860713015290473110591 : (((((True ∧ (((False ∨ p3) ∧ ((p2 → ((True ∧ (p2 ∧ p2)) → (p4 ∧ ((True ∧ (p3 ∨ p4)) ∧ p3)))) → False)) ∧ p5)) ∨ p3) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_179400134850488300129365329492 : ((p3 ∨ (True ∧ (((False ∧ p5) ∨ (((p1 ∧ False) → True) → p2)) ∨ True))) ∨ (((((p1 ∨ p2) ∧ p4) ∨ p4) ∧ p4) ∧ (False ∧ (True → True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_156725244215315683414824377657 : ((((p4 → (((False ∧ p5) ∧ False) ∨ p1)) ∧ ((p5 ∧ (p3 ∨ (p4 ∧ p2))) ∨ (p3 ∨ p3))) ∧ p2) ∨ ((False ∧ False) ∨ (True ∨ (p1 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116970459460062848420000691768 : (((p4 ∧ p1) → (((False ∨ (p3 ∧ (((p2 ∨ False) → (p5 → (False → (((p1 → p2) ∧ p1) ∨ p2)))) → p1))) → p5) → False)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



