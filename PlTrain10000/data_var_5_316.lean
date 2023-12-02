variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609473186734353816941234088886 : (((((False ∧ ((True → ((p3 → p4) ∨ p4)) ∨ ((((True ∨ p1) ∨ ((p3 ∧ False) ∨ (True → False))) ∨ (p2 ∧ p3)) → False))) ∨ p1) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107404840847343875533182568753 : ((((p5 ∨ p2) ∧ True) → ((p1 ∨ (((p5 → (p1 → False)) → p2) → (True ∧ (p4 ∧ (p5 ∨ p3))))) ∨ (True → (p5 ∨ p2)))) ∧ (p4 → p4)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- Implications on the right can always be decomposed.
  intro h8
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149522044181439929951796282229 : ((p1 ∧ (p4 ∧ (p3 → ((p3 ∧ p3) ∧ (p4 ∧ (((True → p4) ∧ (p5 ∨ (p4 ∧ (p1 ∧ p1)))) ∨ False)))))) ∨ ((p2 ∧ False) → (True → False))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192513100392424395408242397532 : ((((p2 ∨ p2) ∨ (False ∨ (True ∧ (p3 ∨ p1)))) ∨ p5) → (p4 → (((((True ∨ True) ∧ ((p3 ∧ p4) → p5)) ∨ False) ∨ True) ∨ (p3 → True)))) := by
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h14 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59266414411685994021055949733 : (((p3 ∨ False) ∨ ((p1 → ((True → p4) → ((p5 ∧ False) ∨ (True ∧ (p3 ∨ ((((False → p3) ∨ p3) → (p4 ∨ p3)) ∧ True)))))) ∨ p4)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659106389955034300338168458986 : ((((p2 → (p3 ∨ ((((True → p2) ∧ p4) → (p2 ∨ (True ∧ (((False ∧ p4) ∨ ((p3 ∧ p2) ∨ p4)) ∧ True)))) ∧ p4))) ∨ (p3 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750639520958725265585019386749 : (((True ∧ (((((p4 ∨ p3) ∨ p4) ∧ (((p5 ∨ p5) ∧ (p5 ∧ p5)) ∧ p2)) ∨ (p1 → True)) ∨ (((p2 ∨ False) ∧ (p5 ∧ False)) ∧ False))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_148501340104278365543433877372 : (((False ∧ (p2 ∧ (((((p3 ∧ p5) ∨ p4) → p5) ∧ p4) ∨ p5))) ∨ (p1 ∧ ((p3 → True) ∧ (True ∨ p5)))) ∨ (p1 ∨ ((p2 ∨ True) ∨ p1))) := by
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
theorem thm_5_vars_178376548548774910033906641871 : ((((p3 ∧ ((True ∨ p2) ∧ (p4 ∧ (True → p5)))) ∨ True) → (True → False)) ∨ ((True → (False → p1)) ∨ (((p3 ∧ True) ∨ p2) ∧ (p3 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53388615471156908557057715831 : ((((p2 ∨ (((p3 → (p5 ∨ p3)) ∧ p2) → (True → True))) → False) → ((p5 ∨ ((p1 ∨ True) ∧ ((p2 ∨ p5) → (True ∨ p1)))) → p3)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (p2 ∨ (((p3 → (p5 ∨ p3)) ∧ p2) → (True → True))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h4
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h12 : (p2 ∨ (((p3 → (p5 ∨ p3)) ∧ p2) → (True → True))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Implications on the right can always be decomposed.
        intro h14
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h15 := h1 h12
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h17 : (p2 ∨ (((p3 → (p5 ∨ p3)) ∧ p2) → (True → True))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- Implications on the right can always be decomposed.
        intro h19
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h20 := h1 h17
      -- False on the left can always be used.
      apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178303324366859839014823311977 : (((((True → (((p1 ∨ p3) → p4) → False)) ∨ True) ∧ p4) ∨ (p4 ∨ p3)) ∨ (((p1 ∨ p5) ∧ p1) → (p5 → (True → (p4 → (p4 ∧ p4)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h11 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680864259484819157286848261715 : (((((p2 ∧ (p3 ∨ p5)) → ((((True → p4) ∨ ((False ∨ (p2 ∨ p2)) ∧ False)) ∨ p5) → (p4 ∧ p3))) → ((p4 ∧ p5) ∨ (p4 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191563477618365084471753205003 : ((p1 ∧ (p5 → ((True → p4) → (p5 → (False ∧ p4))))) ∨ ((((p4 ∨ p2) ∧ p3) ∨ (False → (False → p3))) ∨ (p5 ∨ (p5 ∨ (p3 ∨ p3))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117179683983511725767166463222 : ((True ∧ ((((p4 ∨ False) ∧ (p1 → (False → (p2 ∨ ((p5 ∧ p2) → ((True ∨ True) ∧ (p3 ∧ True))))))) ∧ p1) ∨ (p3 ∨ p5))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1770629787633613269682101147 : ((((((p5 ∨ (p2 → p2)) ∧ p2) ∨ (True ∨ (((False ∨ p5) → p2) ∧ (True ∨ (p4 ∨ p2))))) ∨ p5) → p5) ∨ (p3 → (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693676522027650958400974683488 : (((((((p5 ∧ p4) ∧ (p3 ∨ False)) ∧ (((p1 ∧ True) ∨ True) ∨ True)) ∨ p2) ∨ ((p5 ∧ (p5 ∨ (p4 → ((p5 ∧ p1) ∨ p4)))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355454858358209934933054862998 : (p5 → ((((p1 ∨ ((False → p4) → p2)) ∨ (True ∧ ((False ∧ (False → ((False ∨ p4) ∧ p3))) → p3))) → ((p1 ∧ False) ∨ True)) ∧ (p5 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
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
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213202272509257077747399449774 : ((((False → p3) ∨ p2) ∧ p4) ∨ ((((p5 → (((True ∧ p3) → p2) → (((p3 → p1) ∨ (p3 ∨ p4)) ∨ False))) → (True ∧ p4)) ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178093870109530285742282164171 : ((((p2 ∨ (p1 ∧ ((True → (p3 ∧ (p5 → p2))) ∧ True))) → p1) → p2) ∨ (True ∨ (((False ∧ p4) ∧ (p4 ∨ (p3 ∨ (True ∧ p2)))) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178582201484483988508712846921 : ((((((True ∨ False) ∧ p1) ∨ False) ∧ p3) ∨ ((p1 ∨ p2) ∧ (p3 ∨ True))) ∨ ((p3 ∧ p4) → (((p4 ∨ ((p1 ∨ p2) ∨ p4)) → False) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (p4 ∨ ((p1 ∨ p2) ∨ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136179842083228244002848804146 : ((((((True → p3) → p3) ∨ p4) → p2) ∧ (True ∧ (p3 → (p1 → ((p4 ∧ (p4 → ((p3 ∨ p5) ∨ p4))) ∧ False))))) ∨ (False → (p1 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201227070335042327595972041289 : ((p2 → ((p5 → p1) ∨ (p3 → (p1 → p2)))) → (p1 → ((((p5 ∨ True) ∧ p5) ∨ p1) ∨ (((p2 ∧ p2) ∧ ((p4 ∧ p2) ∧ p4)) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52504463282110828203039507109 : ((((((((p5 ∨ p4) → (p4 ∨ p4)) → p2) ∨ (True ∧ False)) → p5) ∧ p5) ∨ (p5 → ((((p5 → p4) ∧ p5) ∨ p4) ∧ (True → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61596934893094057024617108640 : ((p1 ∧ ((True → (p4 ∧ p3)) ∨ (((p5 → (p2 ∨ (p5 ∧ (p4 → p1)))) ∧ p3) ∨ ((((False ∨ p3) → p4) ∧ p3) ∨ (True ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61674757941736608851324557121 : ((p1 ∧ (p5 ∧ ((p4 ∧ p4) ∨ ((((p2 ∧ ((True → p2) → ((p3 ∨ (True ∨ False)) ∨ (p4 ∧ (p1 → False))))) → p3) ∨ p2) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_900456193346754317004520417433 : (((((p2 → p5) → (p2 ∨ (p2 → ((p4 ∨ (p5 → (((p3 ∨ p5) ∧ True) ∨ (False ∧ (p4 ∧ True))))) ∨ p4)))) → (True ∧ (False ∧ p1))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 → p5) → (p2 ∨ (p2 → ((p4 ∨ (p5 → (((p3 ∨ p5) ∧ True) ∨ (False ∧ (p4 ∧ True))))) ∨ p4)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8648950184383079978357437368 : (((((((True ∨ p3) ∧ (((((p2 ∨ True) ∨ p4) ∧ p3) ∨ p4) ∨ (p4 → ((p3 → True) ∧ False)))) ∧ True) ∨ p5) → (p1 → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114059839305633249447851881360 : ((((False ∨ ((((True ∨ (p5 ∧ p1)) ∨ (True → p5)) ∨ p3) → p5)) → ((p2 → (p4 ∨ False)) ∨ p1)) ∨ (True ∨ (True ∧ False))) ∨ (False ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226302703962113895672585878187 : (((p4 ∨ p4) ∨ p5) ∨ ((((((p2 → True) → False) → (p2 → (p3 ∧ (True ∧ False)))) → (((True ∨ p5) → True) → False)) ∧ (p2 → True)) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p2 → True) → False) → (p2 → (p3 ∧ (True ∧ False)))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (p2 → True) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h7
    -- False on the left can always be used.
    apply False.elim h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h10 : (p2 → True) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h12 := h5 h10
    -- False on the left can always be used.
    apply False.elim h12
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h13 := h2 h4
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h14 : ((True ∨ p5) → True) := by
    -- Implications on the right can always be decomposed.
    intro h15
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h16 := h13 h14
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191136755883366701535002899448 : ((((p5 ∨ p3) ∧ p3) ∨ (p3 ∨ ((p3 → p1) → p1))) ∨ (p1 ∨ ((p4 ∨ ((False → p5) ∨ (p4 ∧ (p4 → p1)))) ∨ ((p2 → p5) ∨ p4)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_457177521970162961005614602138 : (((((p3 ∨ ((((True ∨ (p4 ∨ (p5 ∧ p1))) → ((p5 ∧ p3) → False)) → p1) ∨ p1)) ∧ p1) ∨ ((p1 ∨ (p1 ∨ (p5 ∨ True))) ∨ p5)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343205589326173313183095788449 : (p2 → (((True ∨ False) ∨ p3) → ((((p5 ∧ p5) ∧ (p1 ∧ ((p3 ∨ p3) ∧ p4))) ∧ p3) ∨ (((p5 → (False → p5)) ∧ (False → p1)) ∨ p4)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113716927681877094618903717508 : (((((p3 ∨ ((p1 ∨ p3) ∨ (((p2 ∧ p4) ∧ (False ∧ (p3 ∨ p2))) ∨ (p2 → p4)))) ∧ p1) → (p1 ∧ p2)) → (p2 ∧ p1)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_898719429795414603257751197846 : (((((p4 ∨ (((((p1 ∨ False) ∧ p5) ∨ p2) ∧ True) ∨ ((((p3 ∧ (False → p4)) → p5) ∧ p3) → True))) ∨ p5) → ((p3 → False) ∧ False)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∨ (((((p1 ∨ False) ∧ p5) ∨ p2) ∧ True) ∨ ((((p3 ∧ (False → p4)) → p5) ∧ p3) → True))) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338506310923005948475775011564 : (p1 → (((False ∨ p5) ∧ p5) ∨ (((((False → p3) ∨ p2) → (((p2 → (p2 → (p4 ∧ p4))) ∨ (p5 → p5)) ∧ (p3 → False))) ∧ p3) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((False → p3) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h5
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161138788844266985631315007716 : (((p3 → True) ∧ ((((False ∨ (p1 ∨ (True → True))) ∨ (False ∨ p1)) → (p2 ∧ True)) ∧ (p2 → False))) → (((p2 ∧ True) ∨ (True ∨ p2)) → p3)) := by
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
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h1.left
      let h15 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h18 : p2 := by
        -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
        have h19 : ((False ∨ (p1 ∨ (True → True))) ∨ (False ∨ p1)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h20
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h16, we can now drive its conclusion.
        let h21 := h16 h19
        -- We need to get the left conjuct of h21 based on <expert-advice>.
        let h22 := h21.left
        -- One of the premise coincides with the conclusion.
        exact h22
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h23 := h17 h18
      -- False on the left can always be used.
      apply False.elim h23
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h1.left
      let h26 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
      have h29 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h24
      -- We have shown the premise of h28, we can now drive its conclusion.
      let h30 := h28 h29
      -- False on the left can always be used.
      apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606950973012493862310307203160 : (((((((p5 ∧ p1) ∨ (p3 → ((p3 ∧ False) ∨ (((p2 → True) → (p5 ∧ p1)) ∨ p5)))) → (p4 ∧ ((False ∧ True) ∨ p1))) ∧ p2) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_55268928833302599617125683200 : ((((p2 ∨ False) → (p2 → (True ∧ False))) ∨ ((p3 → ((((True ∧ p4) → (p5 → p5)) ∧ p1) → True)) → (p5 ∨ (p1 ∨ (False ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300955154490874580182279061601 : (False ∨ (((p3 ∧ (((False ∨ True) ∧ p4) → ((True ∧ p3) → False))) ∧ p1) ∨ (p2 ∨ (((p4 ∨ p5) → p1) → (((False ∧ p2) ∧ p2) → p3))))) := by
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
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803115242486825168257417628092 : (((p3 → ((False ∨ (((((True ∨ p2) ∧ p4) ∧ (p2 ∧ (p4 ∧ ((p4 → p3) → (p2 ∨ p1))))) ∨ ((p2 ∨ p1) ∨ p3)) ∨ p5)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51244091057112980139037176949 : (((((p5 ∨ p3) ∧ p3) → ((p3 ∧ ((p4 ∧ p3) → ((False → p5) ∧ p3))) → (True ∧ p4))) ∨ (p1 ∨ (False → (p1 → (p1 ∧ p2))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809994528592856407462272761290 : (((p5 → (((((p1 ∧ p2) ∨ p5) ∨ ((p3 ∧ (p5 → p2)) ∨ (((p5 → (p2 → p1)) ∧ p5) → p4))) → p3) → (p2 ∧ (True ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115768003925263590065165616203 : (((True → (p1 ∧ ((p5 ∧ p5) ∨ p5))) → ((p1 ∧ (p1 ∨ ((p5 ∨ p3) ∨ False))) → ((True → ((p4 ∨ p5) ∧ p1)) ∧ p2))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745545119896883378905010759420 : ((((True ∨ p1) → (((((p5 ∧ False) ∨ (p3 → ((False ∨ (p3 ∨ ((p5 ∧ p1) → p2))) ∨ (False ∨ p3)))) ∧ (p5 ∧ True)) ∨ True) ∧ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685701781639833894357535515990 : (((((p4 ∧ (p4 ∧ ((p3 ∨ p2) ∨ (True ∨ (True → (p5 ∧ (p5 ∧ (p4 → p3)))))))) ∨ p1) → ((((p4 ∧ p1) ∨ p4) ∧ p3) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216749779455605933721233354347 : ((((False → False) → p5) ∧ p3) → ((p3 ∧ ((((p1 → p4) ∧ p1) ∧ p4) ∨ p2)) ∨ (p3 ∧ (((p2 → (p3 ∧ p1)) ∨ (p4 ∨ p5)) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (False → False) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710989468296327358267697890777 : (((((p3 ∧ False) → (p5 ∧ (p1 → p4))) ∧ (p3 ∨ (((p3 → (((p1 → ((True ∨ True) ∨ p3)) ∧ (p1 ∨ p2)) ∨ p4)) ∨ p1) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_35058681459824692818418483941 : ((p1 → ((False ∨ ((p3 ∧ p4) ∨ (p5 ∨ ((p2 ∨ (p1 → p5)) → (p4 ∧ ((((False → p3) → p2) ∨ True) ∨ p2)))))) ∨ (False ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66267902821480881895232566637 : ((p5 ∨ (((True ∧ False) ∧ p5) ∨ (((p3 → (p1 ∧ (p2 → p2))) ∧ ((((True ∧ (True ∧ p2)) → p3) → (p2 ∨ True)) ∧ p5)) ∨ True))) ∨ p5) := by
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
theorem thm_5_vars_173125457695518650565396593192 : ((p2 ∨ ((p4 → p3) → (((True ∨ (p4 ∧ (True → (False ∨ p2)))) ∧ True) → p2))) ∨ (((False → (False ∧ p5)) ∨ True) → ((p3 ∨ False) → p3))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715539524793747569548330911332 : (((((False ∧ (p2 ∨ False)) ∧ p5) ∧ (((True ∨ (((p5 ∨ p4) → ((True ∧ True) ∧ (False ∧ (False → p3)))) ∧ p5)) → (False ∧ p5)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140503904891445354564014853686 : ((((((p1 → p4) ∨ p3) ∧ True) ∨ (((((p5 ∨ p5) ∧ p5) ∧ False) → p1) → True)) ∧ (p1 ∨ ((p2 ∨ p4) ∧ p2))) → (False ∨ (False → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- False on the left can always be used.
          apply False.elim h14
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- False on the left can always be used.
          apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h24
          -- False on the left can always be used.
          apply False.elim h24
        case inr h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h26
          -- False on the left can always be used.
          apply False.elim h26
  case inr h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h28 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h29
      -- False on the left can always be used.
      apply False.elim h29
    case inr h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h33 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h34
        -- False on the left can always be used.
        apply False.elim h34
      case inr h35 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h36
        -- False on the left can always be used.
        apply False.elim h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62380714275436861866522982147 : ((p3 ∧ ((p4 → ((((p2 ∨ False) ∧ p1) ∨ ((p2 → p3) ∨ p3)) ∧ (p5 ∨ p3))) ∨ (((p3 ∧ p3) ∧ True) ∧ (True → (p2 ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189572206622559824448421987778 : ((True ∨ ((p2 ∨ False) → ((p4 ∨ (p5 ∨ p4)) ∧ p3))) ∧ (((p2 ∧ ((p5 → p2) ∨ p5)) ∧ p3) → (((p1 → True) → p4) ∨ (p3 ∨ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200708921155777028311158156672 : ((p2 ∧ (p4 ∧ (((p4 ∧ True) → p1) ∨ p4))) → (p5 ∨ ((((p3 ∨ p1) ∧ False) ∨ False) ∨ ((False ∧ (True → (False ∨ (p1 ∧ p2)))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320131107254504747969846128891 : (p4 ∨ ((True → (p5 ∧ False)) → ((p2 → ((False ∨ (p1 ∨ p3)) ∨ ((p1 ∨ p4) → (False → True)))) → ((p1 → (False ∧ p1)) ∧ (True → False))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57841527824333423173796497404 : (((p5 ∧ (p4 ∨ p3)) → (p1 ∧ (((p5 → p3) → True) ∧ ((((p1 → (((p3 ∧ (p5 ∨ p4)) ∧ p3) ∧ p1)) → True) ∧ p2) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115193217964172978718848082368 : (((((p1 ∨ True) → False) ∨ ((p2 → (p3 ∧ p1)) ∨ p4)) ∧ ((False → ((((False → p1) ∨ (p3 → p1)) ∨ p3) ∨ p5)) → p3)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131039752254427872747920347261 : (((p3 ∧ ((p1 ∨ ((p2 ∧ p1) ∨ (p3 → p2))) → p1)) ∨ ((p4 ∨ (p4 ∨ p5)) ∨ ((False ∨ True) ∨ (True ∧ p2)))) ∧ (p1 → (p4 → p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68972468057393352435863102930 : ((p4 → (p4 → ((p5 → ((((p4 ∨ True) → (p4 ∧ (((((p3 ∨ p1) → p5) → True) ∨ False) ∧ p4))) → p5) ∨ (p4 → p2))) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307793087939868388429883333318 : (p1 ∨ (p4 → (((((((((p4 → False) → p4) ∧ p5) ∧ (p4 ∨ p5)) → (((True ∧ True) ∧ p3) ∨ p3)) ∨ p4) ∧ (p4 ∨ p2)) → p1) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((((((p4 → False) → p4) ∧ p5) ∧ (p4 ∨ p5)) → (((True ∧ True) ∧ p3) ∨ p3)) ∨ p4) ∧ (p4 ∨ p2)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_930422887718124584025897235987 : ((((((p5 → False) ∨ ((p5 ∧ p2) ∨ (p4 → p4))) ∨ p1) → ((p1 ∨ (p2 → p2)) → (((p4 → p2) → (p3 → (p3 ∧ True))) → False))) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 → False) ∨ ((p5 ∧ p2) ∨ (p4 → p4))) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p1 ∨ (p2 → p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : ((p4 → p2) → (p3 → (p3 ∧ True))) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h10
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h11 := h7 h8
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659704267491494334775566304159 : ((((((p2 → p4) ∧ ((((((False ∨ p4) ∨ False) ∧ p4) → (p3 → p2)) ∧ ((True ∨ p4) ∧ p3)) ∧ (True ∧ p3))) ∧ p4) → (True → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670818595703684414023811469122 : ((((p1 ∧ (False ∧ (False ∨ ((((p2 ∧ (p2 ∨ (p2 ∨ True))) ∨ ((p2 ∧ p3) → p3)) ∧ p4) ∧ (p1 → False))))) ∨ (p3 ∧ (p2 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112504532225407504906074758305 : ((((((True ∧ ((p1 ∧ p1) ∨ ((False ∧ (p4 ∧ p3)) ∧ (((p1 ∨ True) ∨ p5) → (p2 ∨ True))))) ∨ p1) ∧ p4) → p3) → p1) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165768272562948092785116233402 : ((((True ∧ (p4 ∨ p1)) ∨ p2) → ((p5 ∨ ((False → p5) → ((True ∧ p5) → False))) → p1)) ∨ (p2 ∨ ((p5 → (p5 ∨ p3)) ∨ (p5 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672232082508796627335721149310 : (((((((((p4 ∨ True) → ((((p3 ∧ p5) ∧ False) → p1) ∨ p4)) ∧ (p5 ∨ (False → p5))) → p3) ∧ False) → p1) → ((p2 ∧ False) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147945547749520726335043118336 : ((((p4 → p2) ∨ ((((p4 → False) ∨ p2) ∨ (p2 → False)) ∨ (((p2 → p3) ∨ True) ∧ p4))) ∧ (True → p3)) ∨ ((p3 → (p2 → True)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148895803865373155098135584903 : (((p2 ∧ (False ∧ (p2 ∧ p4))) ∨ (p5 ∧ (((((p2 ∨ (p2 ∨ (True → p4))) ∨ True) ∨ p5) ∨ p3) ∧ False))) ∨ (((p4 → True) ∧ p1) → p1)) := by
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
theorem thm_5_vars_52974762890233138803088004254 : (((((True → True) ∨ (p5 ∨ ((p4 ∧ (p1 ∨ False)) ∧ False))) → p3) ∧ (((p1 → p4) → (((True ∨ p1) → p3) ∧ (p2 ∨ p4))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300893285758261533325954411113 : (False ∨ ((p5 → ((((False → p3) ∨ False) → ((p2 → p4) ∨ (p1 ∧ p4))) ∨ p1)) ∨ (p2 → (((p2 ∧ (p1 ∨ (True ∨ p3))) → True) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316612107057424351212757973850 : (p3 ∨ (p4 ∨ ((p2 ∨ (p2 ∧ ((((p2 ∧ ((p2 → p3) ∨ (True ∧ p5))) ∧ ((p1 ∧ True) ∧ (p2 ∧ True))) ∧ p2) ∨ (False ∧ p3)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168033414352199745534562487121 : ((((p1 ∨ ((p5 → p3) ∧ p3)) ∨ p2) → (p4 → ((False ∧ p4) ∨ ((False ∨ True) → p2)))) → (((p3 ∧ (p5 → (False ∧ p4))) ∨ p3) → p3)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352036397259455931601288147324 : (p4 → (((p4 ∨ (p4 ∨ p1)) ∨ ((p5 → p2) → False)) → (True → ((p1 ∨ (((((False ∨ p5) ∧ False) ∨ True) ∧ p5) ∨ (p4 ∨ p3))) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126031263440756994044434593452 : (((p2 → p2) → ((((False ∧ (((True ∧ p1) ∨ (((p1 → p4) ∨ True) ∧ (p1 → p3))) ∧ p4)) ∧ p1) ∨ (p4 ∨ p3)) ∧ False)) → (p2 → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p2 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613324984916414124535699004550 : ((((((p4 → (True ∨ p3)) → (p5 ∧ (True ∨ ((p3 ∨ p4) ∨ (p4 → ((p2 ∨ (p2 → p5)) ∧ (False ∧ False))))))) → (p3 ∧ p1)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_200800841336845240059193763537 : ((p5 ∧ (((p5 → p2) → (p1 → True)) ∨ True)) → ((p3 ∨ ((p4 ∨ p1) ∨ ((p2 → (p3 ∧ (p1 → False))) → p1))) ∨ ((True ∨ p5) ∧ True))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749617696257004197856458267287 : (((True ∧ (((True ∧ (p5 ∨ ((((True → p4) ∧ (p5 ∨ ((p5 ∧ p1) ∧ p3))) → (p4 ∨ (False ∧ p1))) → (p1 ∨ p4)))) ∧ p1) ∨ True)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621720600244751241756260390645 : ((((p1 ∧ (((((((((True ∧ (p3 → p1)) ∨ (p4 ∧ p1)) ∨ True) ∧ False) → True) ∧ p2) → p5) → (p3 → (p4 → p1))) ∧ False)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115982857812583254032566123513 : ((((p2 ∧ (True → p1)) ∨ p5) → ((((p3 → p4) ∨ p2) → (True → ((p3 → False) ∨ ((p3 → (p1 ∧ p1)) ∨ True)))) ∨ p4)) ∨ (True ∧ p2)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h5
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
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
theorem thm_5_vars_55816912732457582864020262798 : ((((p3 ∨ p3) → (True → p3)) ∧ ((((False → ((p2 ∨ True) ∨ (p2 ∨ False))) ∧ ((p1 → True) → False)) ∧ ((p3 → p2) ∧ p5)) → p3)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h7.left
  let h11 := h7.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h12 : (p1 → True) := by
    -- Implications on the right can always be decomposed.
    intro h13
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h14 := h9 h12
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625092031807828671957820314554 : ((((True → ((False → ((((p1 ∨ p4) → p2) ∨ p5) ∧ ((((True → True) ∧ (p3 → p5)) ∧ p3) → ((False ∨ p4) ∨ p5)))) → p4)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638974928280529970919189497433 : (((((p2 ∨ (False ∨ (False → p2))) ∧ (((p5 ∨ (False → (((p5 → p3) ∧ p2) → p1))) → False) ∨ ((p5 ∧ (True → p5)) → p3))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671179535167927561277125922865 : ((((p3 ∨ (((p4 ∧ ((p5 → (p4 ∨ (False ∧ p1))) → ((p3 ∨ p2) ∨ (True → (True ∨ p4))))) ∨ p5) ∧ p5)) ∨ (False → (False ∨ p5))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_43644548123175109278017110877 : (((((((p5 ∨ p2) ∧ p5) ∨ (p5 ∨ (((p1 → (True ∧ p2)) ∧ p5) ∨ ((p4 → p1) → (p5 ∨ p5))))) → (True ∨ p3)) → p3) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232376612781544476355470932332 : (((p5 → False) → True) → (((p1 → p1) → (((p3 ∨ ((False → p4) → (p2 ∨ p5))) ∧ p2) ∧ ((p3 ∨ p3) → p5))) ∨ (p2 → (True ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180997737388130227333219129839 : (((p4 ∧ p5) ∨ (p1 → (p1 ∨ ((True ∧ (True ∨ p5)) ∨ (True ∧ p1))))) → (((((p5 ∨ p5) ∨ (p4 → p5)) ∨ p1) ∨ p2) ∨ (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48413092166507276320850718603 : (((p2 → (((((((((True ∧ (p3 → False)) ∨ True) ∨ p2) → p5) ∧ p2) ∧ p2) → True) ∨ p1) ∨ (True ∨ (p3 ∨ True)))) → (p1 ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732706866157337685876441470774 : ((((p1 ∧ p3) ∧ (p1 ∨ (p2 ∨ (p5 ∧ ((((False ∨ p1) → (p5 → p4)) → ((False ∧ p2) ∧ p2)) ∧ (p2 ∨ ((p4 ∧ p1) → p5))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115732043262131635283636436083 : (((((p3 ∨ p2) ∨ p5) ∨ (p3 ∧ p4)) → (p1 ∧ ((p1 ∧ (((p3 ∨ False) → p2) ∧ ((p1 → p3) ∨ p3))) ∧ (p2 ∨ p1)))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350336299554911592096174833449 : (p4 → ((p1 → (False ∨ ((False ∨ ((p4 ∧ p5) ∨ (((((p1 ∨ p3) → p1) → (p3 → (p1 ∧ True))) → False) ∧ False))) ∨ (p1 ∧ True)))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200847729457665667088302628705 : ((True ∨ ((True → (p5 ∧ False)) ∨ (p5 ∧ p1))) → ((((True → p2) → p1) ∨ p4) → (((((p2 ∧ p4) ∧ True) ∧ p5) ∧ p4) → (p4 → p2)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- One of the premise coincides with the conclusion.
        exact h11
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h21 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- One of the premise coincides with the conclusion.
        exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324372374249811507668968068995 : (p5 ∨ (((p4 ∧ p4) ∨ (p1 → (p5 ∨ False))) ∨ (True ∨ (p1 ∨ (True ∨ (p4 ∧ (p1 ∨ (p2 ∧ ((True ∧ p2) ∨ ((False ∧ True) → p5)))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117003677774910366582678471639 : (((False ∨ p1) → (((p5 ∨ (p1 ∧ (p4 ∨ (((((p3 → False) → True) → p2) → False) ∨ (p5 ∧ p1))))) ∧ p5) ∨ (p4 ∧ p5))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65704182236232289031310236068 : ((p4 ∨ ((((((p2 → p2) → (((p5 → p2) → p5) → p1)) ∧ p5) ∨ (p5 ∨ p5)) → (((p5 ∨ p1) ∧ p2) ∧ p1)) ∧ (p2 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328704202692255830535932425404 : (True → (((p1 ∨ (p5 ∧ ((False ∧ p5) ∧ p2))) ∨ (False → (p1 ∨ False))) ∨ (p3 ∨ (((p3 ∨ p5) ∨ (p3 ∨ (False ∨ False))) ∨ (p3 ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308697492952585360598844080477 : (p2 ∨ ((p3 ∨ (((True → False) ∨ ((p5 ∨ (p4 ∨ (p5 → (((p3 ∨ p4) ∧ p4) → p3)))) → (p4 ∧ (True → (p3 ∨ False))))) → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622901200091759411320260315441 : ((((p5 ∧ ((((True ∧ p5) → False) ∧ (p3 ∨ ((((False ∨ p5) ∨ ((False ∧ p2) → p3)) → (p3 ∨ False)) → p5))) ∨ (False ∧ False))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174702903246063477533027488219 : (((p2 ∧ (p4 ∨ p5)) ∨ ((True ∨ p5) → ((p2 → (False ∨ (p4 ∧ p4))) ∨ p5))) → (((p4 ∨ (p4 ∧ False)) → p4) ∧ ((p2 → False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h12
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h17 =>
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
theorem thm_5_vars_738287423341233135138726531007 : ((((False ∧ p5) ∨ (((p4 ∨ p5) ∧ p5) → ((p5 → (p5 ∧ (True ∧ False))) → (((p5 → p2) → (p4 ∨ (p5 → (p2 ∨ p2)))) ∧ False)))) ∨ p3) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h14 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h15 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h16 := h2 h15
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- False on the left can always be used.
    apply False.elim h18
  case inr h19 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h20 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h21 := h2 h20
    -- We need to get the right conjuct of h21 based on <expert-advice>.
    let h22 := h21.right
    -- We need to get the right conjuct of h22 based on <expert-advice>.
    let h23 := h22.right
    -- False on the left can always be used.
    apply False.elim h23
  -- True on the right can always be proven directly.
  apply True.intro



