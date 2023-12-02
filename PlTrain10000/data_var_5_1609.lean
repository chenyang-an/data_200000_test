variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616678985239509284984865074059 : (((((((p1 → (p2 ∨ ((p4 ∨ p2) ∧ False))) ∧ p5) ∧ p2) ∨ (((False → p2) ∨ p3) ∨ ((p3 ∧ p2) ∧ ((p4 → p2) ∧ p4)))) ∨ p3) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_172044602452997830494474613492 : (((p1 → (True → (p3 ∧ ((p3 → ((p5 ∧ False) ∧ p3)) ∧ False)))) ∨ (p3 ∧ p3)) ∨ ((False ∨ p1) ∨ (True → (True ∨ ((p1 ∧ p1) → p1))))) := by
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
theorem thm_5_vars_773592549654436741756226620851 : (((False ∨ (((p2 ∨ p4) ∨ ((True ∧ (p3 ∧ ((((p4 ∧ True) → False) → p1) ∨ ((p2 → p4) ∧ p5)))) ∨ (False → (False → False)))) ∨ p5)) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159715997865490787813740121991 : (((((((False ∧ p2) ∨ p1) ∨ ((True ∨ False) ∧ p3)) → p4) ∨ ((p2 ∨ p5) ∨ (False ∨ p1))) ∨ False) → ((p1 ∨ (p2 ∨ True)) ∨ (True → p5))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
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
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h7 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- False on the left can always be used.
          apply False.elim h9
        case inr h10 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67418681775572715831357503198 : ((p1 → (((p2 → p4) → ((p3 ∧ False) ∨ ((((p2 ∧ p1) → ((True → p3) ∨ (False ∨ p1))) → (True ∧ p5)) ∨ False))) ∨ (p1 ∨ p1))) ∨ p4) := by
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
theorem thm_5_vars_38241526467526105366993612437 : ((((((((p2 → p2) ∧ ((p3 ∧ p4) → p1)) ∨ (True → ((False ∧ p3) ∧ True))) → p4) → False) ∧ (((p1 ∧ p3) → True) ∨ p2)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49922011333688233775547398026 : ((((((p2 → p3) ∨ p3) ∧ (((False ∧ ((False ∨ False) ∧ (p3 ∨ p3))) → True) ∨ (p3 ∨ False))) → p2) ∧ (p3 ∨ (p5 → (True ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181561880802161596226887361111 : ((False → ((True → (p5 → False)) → (p3 ∧ (p5 → ((p5 ∨ p3) ∧ p1))))) → ((((p4 ∨ True) ∧ False) → p3) → ((p2 ∨ p1) ∨ (True ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40796558939681806831465063747 : ((((p5 ∧ (False → ((p4 ∨ (p4 ∨ ((False ∧ ((False ∨ p3) ∨ (p4 → (p5 ∨ ((p5 → True) ∧ p4))))) ∧ False))) → p3))) → p3) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135529586361061955411368365681 : (((((False ∨ p1) → ((p1 ∧ (p2 → (p1 → p2))) ∧ ((p3 ∧ p1) ∨ p5))) → False) ∧ ((p5 → (p4 ∧ p1)) → p1)) ∨ (False → (p4 ∧ p5))) := by
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
theorem thm_5_vars_639633691073718697453936520031 : (((((p2 ∧ (False → p5)) ∧ (p3 → (p5 ∧ (p3 → (((p3 → (((p2 ∧ p4) ∨ p4) ∧ p4)) → True) ∨ ((p1 ∨ False) ∧ p1)))))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693383718518424207795322180365 : ((((p2 → ((((p5 ∨ p5) ∨ (p4 ∧ p3)) → False) ∧ ((False ∨ p4) ∨ p2))) ∧ (((False ∧ (p5 ∨ p3)) ∨ p3) ∨ (p5 ∧ (p2 ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45111934173635679839279653702 : ((((p3 ∨ p2) → (p3 → (p4 → (((((((True ∨ (p5 → ((False ∨ p3) ∨ p5))) ∨ True) → p1) ∧ p1) ∨ p3) ∧ p4) ∨ p4)))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157907557875902108662054080544 : (((((p5 → (p3 ∧ False)) → p3) ∧ (False ∨ (p2 → p2))) → ((p2 ∧ p3) ∨ (True ∧ (p4 ∨ True)))) ∨ ((p3 ∧ ((p5 ∧ p3) → False)) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110830834928611107003203120870 : ((((p1 ∧ (((((p2 ∧ (False ∨ ((p1 ∨ (p1 ∧ p2)) → True))) ∨ p5) ∨ p4) ∧ p1) → (False ∧ (True ∨ p2)))) ∨ p5) ∧ p2) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740849382523108377072193759364 : ((((p3 ∨ False) ∨ ((p1 → p4) → (True ∧ (p4 ∧ (p3 ∧ ((((p1 ∨ p1) ∨ (p4 ∧ p1)) ∨ p5) → ((False ∨ p1) ∧ (p1 → True)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111575758886132854119208808606 : (((((True ∧ p2) → (((((p5 → ((False ∨ ((p4 → p4) → p4)) ∧ (p5 ∨ False))) → False) ∧ p3) → p5) ∨ p3)) ∧ p4) ∨ True) ∨ (p3 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40004653877302313772257200299 : (((p5 → (((True ∨ False) ∧ (p1 ∧ p3)) ∧ ((False ∧ (((p2 → ((False ∧ p2) ∨ p4)) ∧ True) ∧ p2)) ∧ (False ∧ (p5 ∨ p3))))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250682093475316335333468729223 : ((p1 → False) ∨ ((((p2 ∨ (p1 ∧ p2)) ∨ ((p4 ∧ ((False ∧ (True → p2)) ∧ p5)) ∨ False)) ∨ ((p5 → (p1 → (p2 → p5))) ∨ False)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124057363198757529474653691008 : (((((p4 ∧ p3) ∨ True) ∧ ((p1 ∨ (False → (p5 ∨ False))) ∨ False)) → ((p1 → (p5 ∨ (p3 ∨ p1))) → (True ∧ (p1 ∧ False)))) → (True → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p4 ∧ p3) ∨ True) ∧ ((p1 ∨ (False → (p5 ∨ False))) ∨ False)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (p1 → (p5 ∨ (p3 ∨ p1))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218014681935178183255351999313 : (((True ∨ p5) ∧ (True ∧ p3)) → (((p4 → False) ∨ (p5 ∧ p4)) ∨ (p3 ∨ ((p1 → (p3 → (p4 ∧ (p1 ∧ (True → (p5 ∨ p1)))))) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718482802271838353084453324129 : (((((True ∨ (p1 ∨ p5)) → False) ∨ (((p3 ∧ p3) ∨ (False ∧ (((True ∨ p3) → ((p5 ∨ p2) ∧ False)) ∨ (True → p5)))) → (p5 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_958069765981733426120664022374 : ((((False → (p2 ∨ p2)) → ((p4 ∨ ((((p2 → ((p5 ∧ (p3 ∨ (p1 → p3))) ∧ p1)) → p3) ∧ p4) ∨ p3)) ∧ (False ∧ (p3 ∧ p2)))) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → (p2 ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57722979841161732937536453898 : ((((False ∨ p2) → p4) → (((p4 → False) ∧ (p3 → True)) → ((True → ((p3 ∨ (p2 ∨ False)) ∨ (p5 ∧ p3))) → ((p4 ∨ False) → p3)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h2.left
    let h7 := h2.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156954422230755297850653450968 : ((((p2 ∧ (((p4 → (p2 → (p3 → p3))) ∨ p2) ∨ (p3 ∧ True))) ∧ ((p2 ∨ p1) → p1)) ∨ p1) ∨ ((((p1 → p1) ∧ p2) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320325981869070054055455905672 : (p4 ∨ ((p3 ∨ p4) ∨ ((((p5 → p3) ∨ p2) → (False ∨ (((p1 → p5) ∧ False) → (p4 ∧ p5)))) ∨ (True ∧ ((p1 → True) ∧ (False ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- False on the left can always be used.
    apply False.elim h7
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
    -- False on the left can always be used.
    apply False.elim h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h9.left
    let h13 := h9.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718535757750731636768323344220 : (((((True → (False → p5)) → p1) ∨ (((p3 ∨ (((p3 ∧ (True ∨ p2)) ∧ p2) ∨ (False → (False ∧ (False ∧ (p4 ∧ p5)))))) ∧ True) ∨ p2)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694511528574115880548263140007 : ((((False ∧ (((p3 ∧ ((p3 → (p3 ∨ (p4 ∨ p1))) ∨ p5)) ∧ p4) ∨ p3)) ∨ ((((False → (p1 ∨ p5)) ∨ (p3 → p4)) ∧ p3) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134106552847265628131072091943 : ((((((((p5 → p2) ∨ (p2 → p2)) → ((True → False) ∨ True)) ∧ (p2 ∨ (p3 ∨ p2))) → False) ∧ (p5 ∧ p4)) ∨ p5) ∨ (p4 ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50724202920681286428990456416 : ((((False ∨ p5) → (p5 ∨ (True → ((p3 ∧ (p4 ∧ (True ∨ p1))) ∧ ((p4 ∧ (True ∧ p2)) ∨ True))))) → ((p4 ∧ p5) ∨ (p1 → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68144129189976753034699070311 : ((p3 → (((((p4 ∧ (True → ((p1 ∨ (p2 ∨ (True → False))) → (p4 → True)))) → (True → (p2 ∧ False))) ∨ p4) ∨ (p3 ∧ p5)) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184522107009421937730976022608 : (((p4 ∨ (((p5 ∨ p1) ∧ (p5 → p4)) ∧ False)) ∨ (p5 → p5)) ∨ (p5 ∧ ((p2 ∨ True) → ((p4 → ((p2 → (p3 → p3)) ∨ p1)) → p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76771656140198999854661610561 : (((((p2 ∧ ((p2 ∧ (p5 → p1)) ∨ p1)) ∧ (p2 ∧ (False ∨ (False → p4)))) → ((True ∧ (True ∧ p2)) ∧ ((p5 → p4) ∨ p2))) → False) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∧ ((p2 ∧ (p5 → p1)) ∨ p1)) ∧ (p2 ∧ (False ∨ (False → p4)))) → ((True ∧ (True ∧ p2)) ∧ ((p5 → p4) ∨ p2))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h5.left
      let h12 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h5.left
      let h17 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- One of the premise coincides with the conclusion.
        exact h16
    -- Conjunctions on the left can always be decomposed.
    let h20 := h3.left
    let h21 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h21.left
      let h28 := h21.right
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- False on the left can always be used.
        apply False.elim h29
      case inr h30 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h27
    case inr h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h21.left
      let h33 := h21.right
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h34 =>
        -- False on the left can always be used.
        apply False.elim h34
      case inr h35 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h32
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h36 := h1 h2
  -- False on the left can always be used.
  apply False.elim h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300571776847227418231012373653 : (False ∨ ((p4 ∨ (((((((p5 ∨ True) ∨ p2) ∧ p5) → (p2 ∨ p4)) ∨ True) ∨ ((p2 ∨ p1) → p4)) ∨ p4)) ∨ ((p5 ∨ False) → (p4 ∨ p5)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782533076539234578356282612814 : (((p3 ∨ ((True ∧ ((p2 ∧ p4) ∨ (((p1 ∨ ((p5 ∧ (False ∨ p2)) ∧ p3)) ∧ ((p4 → p1) ∨ (p2 → p1))) ∨ (p4 ∨ False)))) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_39385677979930956925231780555 : (((p3 ∧ (p1 ∨ ((p5 ∧ ((p1 ∧ (((p2 → p3) ∧ p3) ∨ ((p5 → (p2 ∨ p4)) → ((p2 → p4) ∨ False)))) ∨ p4)) ∨ p4))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62443886139192280053999396554 : ((p3 ∧ (((p3 → p4) ∨ p2) ∨ (((p4 → ((((p5 ∧ (False → False)) ∧ p4) ∧ False) ∧ (p1 ∨ ((p5 → p1) → p2)))) ∨ p4) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330844018623742125545755234373 : (True → (p3 → ((((True ∧ (True ∨ p5)) → False) ∨ (((False → p1) → ((False ∧ p4) ∧ p1)) ∧ ((((p1 ∨ p2) → p3) ∨ p4) → p5))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48331055378733132482352367632 : (((p1 ∨ (p1 → ((((p4 ∨ ((p4 → (p1 ∨ p2)) ∨ (((p1 → p2) ∨ False) ∨ p4))) ∧ p3) ∧ p1) → (p4 ∨ True)))) → (p3 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207492306732631187261953210476 : (((p4 → ((p3 → True) ∨ p3)) ∨ p1) → (((p2 → (p3 ∧ False)) ∨ (((p5 ∨ p3) ∧ ((p1 ∧ p5) ∧ (True ∨ False))) → True)) ∧ (p2 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177935585217856909341411439180 : (((((p5 → True) ∧ (p1 ∨ p1)) → ((p3 → p5) ∧ (p5 ∧ p1))) ∨ True) ∨ ((p2 ∧ (True → (p2 ∨ (p4 ∧ ((True ∨ False) ∧ p1))))) ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191545452805958339742005224909 : ((p1 ∧ ((p2 ∧ ((p2 ∧ True) ∧ False)) → (p4 ∨ p5))) ∨ (((True ∨ (p3 ∨ False)) ∨ True) → (((p5 ∨ p4) ∧ p5) ∨ (False → (False ∨ False))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
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
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39278225708839977435239047706 : (((p1 ∧ ((((p3 ∧ ((((p3 ∨ True) → ((p5 ∨ p3) ∨ p1)) ∧ (((False ∨ False) ∨ p4) → p2)) → p3)) ∨ p3) → p4) ∨ True)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51873746329085031652796545079 : ((((p2 ∧ (((((((p1 → p1) ∨ p1) ∧ p1) ∧ p5) → False) ∧ True) ∧ p3)) ∨ True) ∨ ((p1 ∨ ((p1 ∧ p4) ∨ (p1 → p3))) ∨ p3)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262437873983523992476286825716 : (True ∧ ((p5 ∧ (((p5 → p5) → ((p2 ∧ (p5 ∧ p2)) ∧ (((((p4 → (p1 ∧ p1)) → False) ∨ False) ∨ p3) ∨ (p4 ∨ p3)))) ∧ p1)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51056215331767654959972102043 : (((p5 ∨ ((p4 ∧ (((p5 ∨ p3) ∨ (p1 ∧ ((p3 → p5) → True))) → (True → True))) ∨ True)) ∧ ((True → (p5 ∧ (True ∧ False))) → p3)) ∨ p3) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354660078637895920987551455575 : (p5 → (((((p5 ∧ p1) → p3) ∧ ((((p5 ∧ (p1 → (((p3 → (p4 → p3)) ∧ p3) → (p5 → p2)))) ∨ p3) ∨ p1) ∧ True)) → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616003291560779576231631128982 : ((((((p4 ∨ (((True ∧ True) → p5) → (False ∧ p2))) → ((p3 → p2) → False)) → (((True ∨ p3) → False) ∧ (False ∨ (p2 → p2)))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_731671666646212910930893795403 : ((((p2 → (p3 ∧ False)) → ((((((((p4 ∨ (p4 ∧ (True ∨ p4))) → p2) → p4) ∧ p5) → p4) ∧ True) ∧ p4) → ((p3 ∧ p3) ∨ p4))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137194070415301730697460559136 : ((False ∧ ((p1 → p3) → ((p2 ∧ p4) ∨ (True → ((False → (p3 ∧ (p3 → ((False → p5) ∧ True)))) → (p1 ∧ p5)))))) ∨ (p4 → (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324492858176415781940169557170 : (p5 ∨ (((False ∨ p3) ∧ (p5 ∨ p2)) ∨ (((p1 ∨ False) → ((((((True → (p4 ∨ p2)) → p2) → p5) → p1) ∨ (p2 ∨ p5)) ∧ p1)) ∨ p2))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353881958432935350333307323468 : (p4 → (p1 → (p3 ∨ ((((p4 → (False ∨ (((p1 ∧ (p3 ∨ p2)) ∨ p4) → False))) ∨ p2) → (p5 ∧ p2)) ∨ ((False ∧ p5) → (p2 ∧ p4)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198460395876441723772801721532 : ((p5 ∧ ((p2 ∨ p5) ∨ (False ∧ (p5 ∨ p3)))) ∨ (False → (((((True ∧ p2) ∨ p3) ∨ p4) ∨ (p4 → (p5 → True))) ∧ ((p3 ∧ True) ∨ p3)))) := by
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
theorem thm_5_vars_347022256259133584836254840790 : (p3 → ((True ∧ ((((((p2 ∨ p2) ∨ p5) → p5) ∧ (p3 ∨ p2)) ∧ p3) ∨ (False ∧ False))) ∨ ((((False ∨ True) ∨ p3) ∨ False) ∧ (p3 ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207868788507075296212394287016 : ((((p1 → p2) ∨ p1) ∧ (True ∨ p3)) → ((False ∧ p4) ∨ (p1 ∨ (True ∨ ((p4 ∨ p4) → (((p3 ∧ p2) ∨ ((p2 ∨ p3) → False)) ∧ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46849977731919833848706939748 : (((((p2 ∨ p5) ∧ (((p5 ∨ True) ∧ (((p3 ∨ (True ∨ p5)) ∨ ((p1 ∨ p4) ∧ (True → p4))) → p1)) → p1)) ∧ True) ∨ (True ∨ p1)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136002199465816532504000254245 : (((p1 ∨ (((p4 ∧ p5) ∨ (True → (p5 ∨ p1))) ∨ p1)) ∨ ((((False → False) ∧ (True → False)) ∨ (p5 → p5)) ∧ p1)) ∨ (True ∨ (p4 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149863906383093818762798939194 : ((p2 ∨ (((p5 ∨ (((p4 ∨ (p5 → (p5 → (False ∨ p5)))) ∧ (p2 ∨ (p5 ∨ True))) ∨ p3)) ∨ p1) ∨ p3)) ∨ (p4 ∧ (False ∧ (False ∨ p3)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89142626009901749482050909793 : ((((p3 ∧ False) → p2) ∧ (((p1 ∧ p4) ∧ p2) ∧ (p2 ∧ (True ∨ ((p3 ∨ p5) → (False ∨ ((p4 ∨ p3) ∨ ((p3 ∨ p3) ∧ p2)))))))) → p2) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h5.left
  let h11 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190935679547818974094554270232 : ((((p3 → (True ∨ p1)) → False) ∧ (p5 ∧ (False ∧ p2))) ∨ ((p2 → (((False ∨ p2) ∧ True) ∨ ((True ∨ (False ∧ True)) → p5))) ∨ (p3 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68630640189586728110091822596 : ((p4 → ((p3 ∨ ((((p1 → p3) ∨ p5) ∧ (p4 ∨ (((p4 ∨ p5) → ((p2 ∨ (p5 ∨ p5)) ∨ (p4 ∨ p5))) ∧ p5))) → False)) ∨ p4)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330781844384236317811025330123 : (True → (p2 → (((((((p4 ∧ p4) → p1) → p3) → p5) → ((True → ((False ∨ p1) ∧ (True ∨ (True → p3)))) → p4)) ∨ (p2 → p4)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234312411735173196986683778947 : ((p1 → (p1 ∧ p1)) → ((p4 → (((p4 ∨ p3) ∨ p1) → ((p3 ∧ ((p3 ∧ (p5 ∨ p2)) ∧ (((p5 ∨ p5) ∨ p2) ∨ False))) ∨ True))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
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
theorem thm_5_vars_323786970644845840066080370903 : (p5 ∨ (((p1 ∨ (((False ∧ (p2 ∧ (p5 → (p1 → (p5 ∨ p4))))) ∨ (p5 ∧ p1)) → True)) → p3) ∨ (((p4 ∧ p4) ∨ p2) ∨ (p1 ∨ True)))) := by
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
theorem thm_5_vars_586910890384370497335904134754 : (((((p1 ∨ (((((p5 ∨ (p4 ∨ (False → (p4 → p5)))) → (p3 → (p3 ∨ p1))) ∨ True) → (p5 ∧ (p4 ∨ p3))) → p4)) ∧ p3) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315008216535677992031324495050 : (p3 ∨ ((((p2 ∨ (p3 ∧ p4)) ∨ (p3 → p5)) ∨ p4) ∨ ((p2 → ((p5 ∨ (p1 ∨ ((p3 ∨ p4) ∨ (p2 → (p2 ∨ True))))) ∧ p4)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56411905728167710931006993249 : ((((p2 → (False → p4)) → False) → ((p5 ∨ (((((p1 ∧ p5) → p2) → p5) ∨ p4) ∨ (p1 ∨ (True ∨ ((True ∨ True) ∨ p4))))) ∨ p2)) ∨ p3) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136646902366026823125842823175 : ((((True → True) → False) → ((False ∧ (((p4 → ((p2 ∨ (p1 → p3)) ∨ p2)) → False) ∨ (False → True))) ∨ (True ∧ False))) ∨ ((p1 ∧ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_443429314749551241877334053422 : (((((p3 ∧ ((p3 ∧ ((p5 ∨ (False ∧ True)) ∧ p2)) ∨ True)) ∨ (p5 ∧ ((p2 → (p4 → (p4 ∧ p1))) → p5))) ∨ ((False → True) ∨ p4)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_38541381652518119772388354237 : ((((((p1 ∨ (True ∧ (p4 ∨ p4))) ∨ p3) ∨ (p4 ∨ p1)) ∧ (((p4 → p2) ∨ (p1 ∧ p2)) ∨ ((p2 → (False → p3)) ∨ p3))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140104794260406402748582862671 : (((p4 ∨ ((((p4 ∨ p2) ∨ (p4 → p5)) ∨ p3) → (p5 ∧ (False ∧ (p1 ∧ ((False → False) ∧ p5)))))) ∨ (True → p3)) → ((True ∧ p5) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701045428415328792136657953315 : ((((((p3 → ((p4 ∧ (False → p4)) ∨ p5)) ∨ p5) → p5) ∧ (False ∨ (p3 ∧ (((p2 ∨ (p2 ∧ (True ∨ (p3 ∧ True)))) ∨ True) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797353556513257800128305735418 : (((p1 → (((False ∧ (p1 ∨ ((p1 ∧ p2) ∧ (p3 → p5)))) ∧ ((p1 → ((p5 ∨ p3) → (p4 → False))) ∧ (p4 ∧ (p4 → False)))) ∨ True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203817104831888967514806905599 : ((True → (p1 → ((p2 ∧ False) → False))) ∧ (p3 → (((p4 ∨ p3) → ((False ∨ (p3 → False)) ∧ ((p5 ∨ p1) → p4))) ∨ (False → (p2 ∧ p5))))) := by
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
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625998179194383485094657092509 : ((((p2 → ((True → (((p1 → p2) ∧ True) ∧ p1)) → ((False ∧ (((p4 → p1) ∧ False) ∨ ((p4 ∧ p5) ∧ (p4 ∨ p1)))) ∧ p3))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_357507659493494722833893991435 : (p5 → (True ∧ (((True ∧ (p3 ∨ ((p2 ∧ ((True → (p1 ∨ False)) ∨ p3)) ∨ p4))) ∧ (p2 ∧ p5)) → ((p5 ∧ (p3 ∨ p5)) ∧ (False ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h4.left
    let h9 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h4.left
        let h16 := h4.right
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h4.left
        let h19 := h4.right
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h4.left
      let h22 := h4.right
      -- One of the premise coincides with the conclusion.
      exact h1
  -- Conjunctions on the left can always be decomposed.
  let h23 := h2.left
  let h24 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h25 := h23.left
  let h26 := h23.right
  -- Disjunctions on the left can always be decomposed.
  cases h26
  case inl h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h24.left
    let h29 := h24.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h27
  case inr h30 =>
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h24.left
        let h36 := h24.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h37 =>
        -- Conjunctions on the left can always be decomposed.
        let h38 := h24.left
        let h39 := h24.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h37
    case inr h40 =>
      -- Conjunctions on the left can always be decomposed.
      let h41 := h24.left
      let h42 := h24.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  -- Conjunctions on the left can always be decomposed.
  let h43 := h2.left
  let h44 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h45 := h43.left
  let h46 := h43.right
  -- Disjunctions on the left can always be decomposed.
  cases h46
  case inl h47 =>
    -- Conjunctions on the left can always be decomposed.
    let h48 := h44.left
    let h49 := h44.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h48
  case inr h50 =>
    -- Disjunctions on the left can always be decomposed.
    cases h50
    case inl h51 =>
      -- Conjunctions on the left can always be decomposed.
      let h52 := h51.left
      let h53 := h51.right
      -- Disjunctions on the left can always be decomposed.
      cases h53
      case inl h54 =>
        -- Conjunctions on the left can always be decomposed.
        let h55 := h44.left
        let h56 := h44.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h55
      case inr h57 =>
        -- Conjunctions on the left can always be decomposed.
        let h58 := h44.left
        let h59 := h44.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h58
    case inr h60 =>
      -- Conjunctions on the left can always be decomposed.
      let h61 := h44.left
      let h62 := h44.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h61



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_460322978263658869090662287 : ((p1 → (((((p1 ∨ p2) ∧ ((p4 → (p5 ∨ (p4 ∨ p3))) → p5)) → p3) ∨ (p3 → (p3 ∧ (p2 ∨ p1)))) ∨ (False → p3))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207963748622507717346313452335 : ((((p1 ∧ p5) ∧ p3) ∨ (True ∧ p3)) → (p5 ∨ ((((p3 ∨ p5) → (p1 ∧ ((True → (True ∧ p1)) ∧ p4))) ∧ p4) ∨ (True ∧ (p4 ∨ p3))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703170234829062570662372022316 : (((((p5 → False) → ((True ∨ (p2 ∧ (True ∨ False))) ∧ p3)) ∨ (p2 ∧ ((p3 → ((p5 ∧ p2) ∨ (p2 ∨ p5))) → ((True → p5) ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683643631182751266834944610669 : ((((((p1 ∨ (((True ∧ p5) ∨ p2) → p2)) ∨ (((False → (True → p3)) ∧ p5) ∨ p1)) ∧ p3) ∨ (p1 ∨ (p3 → (p3 ∨ (p2 → p1))))) ∨ False) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133843950438168587853872556399 : (((True ∧ ((p2 ∧ (((((p5 ∨ False) → p4) → ((p5 ∨ p2) ∧ p3)) ∧ (False ∨ p3)) ∨ True)) ∧ (p5 ∨ True))) ∧ False) ∨ (True ∨ (p1 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618737320336888260590803992838 : ((((((p4 ∧ True) → True) ∧ (((((p3 ∨ p5) → (p1 ∧ False)) → ((p2 ∨ p1) → ((p5 ∨ p1) ∨ p5))) ∧ (True ∨ p3)) → p3)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_228072078864907001345683191494 : ((p4 ∧ (p4 ∧ p2)) ∨ (False ∨ (p3 → (((p2 ∧ (p4 → (False ∧ p4))) ∨ (p3 ∨ (p3 ∧ p1))) ∨ ((p2 ∧ (p2 → p3)) ∧ (True ∧ False)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158786037993477530559616910744 : ((p5 ∧ ((((p3 ∨ (p1 ∧ (p2 → (p1 ∨ ((p4 → p1) ∧ p5))))) ∧ (p1 ∧ p2)) → False) → p2)) ∨ (p1 → (((p4 ∨ p1) → p2) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45046760705336291883183729694 : ((((True → p4) ∨ (p4 ∧ (((p2 ∧ (p4 ∨ False)) ∧ ((p1 ∨ p4) → p1)) ∧ (((p3 ∧ p2) ∧ p2) → ((p4 → True) ∧ p5))))) → p4) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199305697457741330723681822835 : (((((False ∨ True) ∧ (p5 → False)) ∨ True) ∨ False) → (((p4 ∧ p2) ∨ (p4 → False)) ∨ (((p3 ∨ True) ∨ (p5 ∨ (False ∨ p3))) → (False ∨ True)))) := by
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
      cases h4
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h11 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h14 =>
            -- Disjunctions on the left can always be decomposed.
            cases h14
            case inl h15 =>
              -- False on the left can always be used.
              apply False.elim h15
            case inr h16 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h24 =>
          -- Disjunctions on the left can always be decomposed.
          cases h24
          case inl h25 =>
            -- False on the left can always be used.
            apply False.elim h25
          case inr h26 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
  case inr h27 =>
    -- False on the left can always be used.
    apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61343968524081691246527089711 : ((p1 ∧ ((((True ∨ p4) ∧ ((p4 ∧ p2) ∧ (((((p4 → (True ∧ p5)) ∨ False) ∨ (p4 ∧ True)) ∨ p3) ∧ p1))) → (False ∧ p2)) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345359626992303000957008974764 : (p3 → (((((p3 → ((((p2 ∨ ((True → True) ∧ p1)) ∨ ((p5 ∧ (p3 ∧ p3)) → p4)) → p4) ∧ p3)) → (p2 → p5)) → p2) ∨ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171564643007215098393629970094 : ((((p3 → (True ∨ ((((p5 ∧ True) ∧ p5) ∧ p4) → (p3 → False)))) → p4) ∨ True) ∨ (p4 → ((p4 → (p4 ∨ (True ∧ (p2 → p5)))) → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42080446399546706955899033610 : ((((p2 → p1) ∨ (p3 ∧ ((p4 ∧ ((p2 → p2) → p1)) ∧ ((True ∨ (p1 → False)) ∧ ((p4 ∧ (p5 ∨ (p2 ∧ p1))) → p5))))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257821179950882402685805423942 : ((p3 ∨ p5) → ((p2 ∧ ((p4 → True) ∧ p3)) → ((p5 → False) → (((p3 → ((False ∨ p3) ∧ p4)) ∨ (p2 ∧ (False → (p3 ∧ p4)))) ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h9
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- False on the left can always be used.
    apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h2.left
  let h14 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h14.left
  let h16 := h14.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h17 =>
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h18 =>
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180760238373734105994373035574 : (((p1 → (p2 ∧ (p4 ∧ p1))) ∨ (((p1 ∨ p1) ∧ False) ∧ (p2 → p4))) → ((((p2 → True) → p3) ∧ (p2 → (p1 ∧ (False ∨ p2)))) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : (p2 → True) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h6
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62275805580134340040190536409 : ((p3 ∧ (((p1 ∧ ((p2 ∧ (p4 ∧ ((p5 ∧ False) → (((p1 → False) ∨ True) ∧ p4)))) → p4)) ∨ (p5 → ((False → p4) ∨ True))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147368957536033212062643514438 : ((((((True ∧ p5) → (p1 → (p2 ∧ (p5 ∧ (p4 ∨ p5))))) ∨ p4) ∨ ((p3 ∨ p1) ∨ (p4 ∧ p5))) ∨ True) ∨ ((p3 ∨ True) ∧ (p5 → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253091637827676906876980816209 : ((True ∧ p4) → ((p2 → p4) → (p3 → ((p2 → ((p2 → (True ∧ ((p3 ∧ p2) → p4))) ∧ (p5 ∨ (p1 ∧ p5)))) ∨ ((True → p3) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311309721940815970480462426775 : (p2 ∨ (True ∧ (p4 → (p3 → (((False → True) → (((True ∧ p5) → True) ∧ ((((p3 ∨ p2) ∧ p4) ∨ (p3 → (False ∧ True))) ∧ p2))) → p2))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (False → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158891727859664714038442762260 : ((p1 ∨ ((((p4 ∧ ((p5 ∧ p1) ∨ p2)) ∨ (p4 ∨ p2)) ∧ (True ∨ (p2 → (p4 ∨ p3)))) ∧ p3)) ∨ ((p4 → (p3 → (p3 → p3))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719060389367079724434248916851 : ((((True ∧ ((p4 → p4) → p4)) ∨ (((((p5 → p2) ∧ (p3 ∧ True)) ∨ True) ∧ p5) ∨ ((((True ∨ False) ∧ p4) ∧ p1) → (p5 ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187041995451386623305280243671 : (((p1 ∧ p5) ∧ (((p3 → True) ∨ (p1 ∧ (True ∨ p4))) ∨ True)) → ((False ∨ (True ∧ ((p5 → False) → p3))) ∧ (p5 ∨ (p4 ∧ (False ∨ p5))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h8
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h10 := h8 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h15
        -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
        have h16 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h15, we can now drive its conclusion.
        let h17 := h15 h16
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h19
        -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
        have h20 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h19, we can now drive its conclusion.
        let h21 := h19 h20
        -- False on the left can always be used.
        apply False.elim h21
  case inr h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h23
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h24 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h25 := h23 h24
    -- False on the left can always be used.
    apply False.elim h25
  -- Conjunctions on the left can always be decomposed.
  let h26 := h1.left
  let h27 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h28 := h26.left
  let h29 := h26.right
  -- Disjunctions on the left can always be decomposed.
  cases h27
  case inl h30 =>
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h31 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h29
    case inr h32 =>
      -- Conjunctions on the left can always be decomposed.
      let h33 := h32.left
      let h34 := h32.right
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h35 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h29
      case inr h36 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h29
  case inr h37 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152065143292441164108179123247 : ((((p4 ∨ p1) ∧ ((p1 → (p2 → (p3 → False))) → p2)) ∨ ((p2 ∨ (False ∧ (False ∨ p4))) ∧ (p5 ∧ True))) → ((p2 → False) ∨ (True ∨ False))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- False on the left can always be used.
      apply False.elim h14



