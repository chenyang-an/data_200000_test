variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200161430578242882773055719100 : ((((False → p4) ∨ True) ∨ (p2 → (p2 → p3))) → ((((p1 → (p5 ∨ (p3 ∨ (p4 → (p5 → True))))) → p4) ∨ (p4 ∧ (p1 ∧ p2))) ∨ True)) := by
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
theorem thm_5_vars_150016731040245337540873818114 : ((p5 ∨ ((p1 → ((p4 ∧ p1) ∨ ((((p5 ∧ p5) ∨ (p1 ∨ False)) ∧ p5) ∨ p2))) ∧ ((p2 ∧ p4) ∨ p3))) ∨ (((False → p5) → True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68434126131006032249866318998 : ((p3 → ((p3 ∨ p4) → ((p3 ∧ p2) ∧ (p1 ∨ (p5 ∨ (p5 → ((p1 ∨ (False ∨ ((p3 ∧ p3) → p4))) ∧ ((p2 ∧ p1) ∨ True)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264496329471320587786410500277 : (True ∧ (((True → p2) → True) ∧ ((True → (((((p5 ∧ (p3 ∨ False)) → (p2 ∨ p2)) ∨ (p1 ∧ p1)) ∧ (p3 ∨ p5)) → (p3 ∧ False))) ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40309883309425502211733263659 : (((((((p2 ∨ ((p3 → False) ∨ (p1 ∧ (p1 ∧ p1)))) ∨ p4) → ((p5 → (p2 → (p1 ∧ (p2 ∨ p5)))) ∨ False)) ∧ p3) ∨ p2) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247456061436865496948793846176 : ((False ∨ p2) ∨ (True → (p5 → (p4 ∨ ((((p4 → p4) ∧ (p1 ∨ (p2 → p4))) ∧ ((((p5 ∧ p1) ∧ p3) ∧ p5) → (p4 → p2))) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_48079043277707419740328237119 : ((((((p4 ∧ False) ∨ (True ∨ p1)) → p3) ∨ ((p5 ∧ (p5 → (p1 ∨ (((p3 ∨ p4) ∧ p1) → (p1 ∧ p4))))) ∨ False)) → (p4 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50887486268578725677235724484 : (((((p1 → (False ∨ (p4 ∧ p4))) → ((((False ∨ (True ∨ p5)) ∨ p1) ∨ p4) ∧ p3)) → True) ∧ (((p4 ∨ (p1 ∨ False)) ∧ p4) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204498299526671937528545233152 : ((((p3 ∧ (p1 ∧ p3)) ∨ p3) ∨ p4) ∨ ((p3 → ((False ∨ p1) ∨ p3)) ∨ (p2 ∧ ((((p3 ∨ p5) ∨ (p4 ∧ True)) ∨ False) ∧ (p3 → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149378862090777221433917906967 : (((p3 → False) → (((((p1 → (p4 ∧ False)) ∨ p5) ∧ (p3 ∧ (((p2 ∧ p3) ∨ p1) → p3))) → p2) → p2)) ∨ (((p5 ∧ p1) ∨ p5) → p5)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149693575355560106483132958487 : ((p5 ∧ ((((p5 ∧ True) ∧ (False ∨ (p4 ∧ (p2 ∨ p2)))) → False) ∨ ((((True ∧ False) ∧ p4) ∧ p4) ∨ p1))) ∨ (False → (p5 → (True ∧ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677549312804531763106114979088 : (((((p2 ∨ ((p5 ∨ (p5 ∧ p2)) → (((p2 → False) ∧ ((False ∨ p4) ∨ p3)) ∧ (p3 ∨ p4)))) ∨ True) ∨ ((True ∧ p2) ∧ (p2 → p1))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656306963303384624394161510624 : ((((((p5 ∧ ((p1 → ((p2 ∨ (p5 → p3)) ∨ False)) ∧ True)) → p1) ∨ (((p2 → p2) ∨ p3) ∧ ((p4 ∧ False) ∨ p4))) ∨ (True ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674891314409566936875423853952 : ((((((True ∧ (p2 → ((((p2 → p4) ∨ (p4 → p1)) → (p3 ∧ (p4 → p5))) → False))) ∨ p3) ∧ p3) ∧ ((p5 ∧ (p4 ∨ False)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257146467456822849873369689939 : ((p2 ∨ p1) → ((((True → (False ∨ ((p3 ∨ (p3 ∧ True)) → p5))) → p1) ∨ p5) ∨ (p4 → ((True ∨ True) → (p4 ∨ (p4 ∧ (p1 ∨ False))))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187630568194109265263633273191 : ((p5 ∨ (((((False ∨ p1) ∧ True) ∨ (p2 → p5)) → p5) → p4)) → ((p4 → p4) ∧ ((True ∨ True) ∨ (p2 ∧ (((p2 ∧ p2) ∧ p3) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187520717038025533428601290881 : ((p1 ∨ ((p1 ∧ True) ∧ ((p3 → p3) ∧ ((p2 ∧ True) ∧ True)))) → (((p2 ∧ (p3 ∨ ((p2 ∧ p3) ∨ False))) ∨ (p4 ∧ (p1 ∨ p4))) ∨ p1)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h5.left
    let h9 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47352751486263888962325531251 : ((((False ∧ p1) ∨ ((p3 ∧ (p1 ∧ p4)) ∧ ((True ∨ (p3 ∨ p1)) → ((True ∨ (False → p5)) ∨ (p5 ∧ (p3 → False)))))) ∨ (p1 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309373709716821841880689019257 : (p2 ∨ (((p2 → True) ∧ (((False ∧ ((p2 ∨ ((False → False) ∨ (False ∧ False))) → p5)) ∨ (((p1 → True) → True) → p2)) ∧ p3)) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58871045519076993437359775063 : (((False ∧ True) ∨ (p3 ∨ ((((True → p5) ∨ p2) → ((p5 ∨ ((p1 ∧ ((p5 ∨ False) ∨ p5)) ∧ p5)) ∨ (True → (False ∨ p4)))) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136795107219605749045356621337 : (((p2 → True) ∧ (p4 ∨ (False ∨ (p1 ∨ ((((False ∨ p2) ∧ (False → (True ∨ p1))) → p5) ∧ ((p4 ∨ p1) ∧ False)))))) ∨ ((True → True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114677491970330835791654782915 : (((p4 ∧ ((((((p2 → p2) ∧ True) → (p5 → (True ∨ False))) → p5) ∨ p1) → p2)) ∨ ((p1 → (True → p2)) ∨ (p3 ∨ True))) ∨ (p5 ∧ p2)) := by
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
theorem thm_5_vars_786429159736467088931252986326 : (((p4 ∨ ((p1 ∧ (((p2 → True) ∨ (p1 → p3)) ∧ (p4 ∧ ((p1 ∧ p2) ∨ p5)))) ∨ (((p4 ∧ p1) ∧ ((False ∧ False) ∧ p1)) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56701335344764801275926646123 : ((((p2 ∧ p2) ∨ False) ∧ ((((p1 → p2) ∨ (True ∨ (((p5 ∧ p1) ∨ True) ∨ ((False ∧ p4) ∨ (False → (p4 ∨ p5)))))) ∧ p5) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_240019973463038461725208907970 : ((p4 ∨ True) ∧ (((p3 ∧ (((p1 ∧ False) ∧ p1) → False)) ∨ ((p5 ∧ (True → p5)) ∨ p2)) → ((p5 ∧ (False ∧ p2)) ∨ (p1 → (True ∨ False))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129286294441696423060982764994 : ((((p5 → (p5 ∧ (False ∧ p2))) → ((((False ∨ ((p4 ∨ (p1 → (p3 → True))) ∨ p4)) ∧ p5) ∧ p1) → p3)) ∨ p1) ∧ ((False → False) → True)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h11 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h12 := h1 h11
        -- We need to get the right conjuct of h12 based on <expert-advice>.
        let h13 := h12.right
        -- We need to get the left conjuct of h13 based on <expert-advice>.
        let h14 := h13.left
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h16 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h17 := h1 h16
        -- We need to get the right conjuct of h17 based on <expert-advice>.
        let h18 := h17.right
        -- We need to get the left conjuct of h18 based on <expert-advice>.
        let h19 := h18.left
        -- False on the left can always be used.
        apply False.elim h19
    case inr h20 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h21 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h22 := h1 h21
      -- We need to get the right conjuct of h22 based on <expert-advice>.
      let h23 := h22.right
      -- We need to get the left conjuct of h23 based on <expert-advice>.
      let h24 := h23.left
      -- False on the left can always be used.
      apply False.elim h24
  -- Implications on the right can always be decomposed.
  intro h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44291436808991791964212518728 : (((((p4 ∨ ((((p3 ∨ p4) → p3) → p1) → p1)) ∨ (p3 → ((True → p5) ∨ p2))) ∧ (p5 ∧ (p2 ∧ (True → (p3 → p3))))) → p5) ∨ p2) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h3.left
      let h7 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h3.left
      let h12 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h3.left
    let h17 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41386968489995652818670553104 : (((((p1 ∨ ((p5 → True) ∧ (((p3 → p2) → p5) ∨ True))) ∧ (True ∨ False)) ∧ ((False → (p4 → p2)) → ((p2 ∨ p4) ∧ p3))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186471085456470687692831023532 : ((((((False → True) ∨ True) ∨ True) ∨ (False → True)) ∧ (True ∧ p1)) → (((True → (p5 ∨ ((False → p5) → (p3 ∨ p5)))) ∨ p5) → (p3 ∨ p1))) := by
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
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Conjunctions on the left can always be decomposed.
          let h9 := h5.left
          let h10 := h5.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h5.left
          let h13 := h5.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h13
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h5.left
        let h16 := h5.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h5.left
      let h19 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h19
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h1.left
    let h22 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h22.left
          let h27 := h22.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h27
        case inr h28 =>
          -- Conjunctions on the left can always be decomposed.
          let h29 := h22.left
          let h30 := h22.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h30
      case inr h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h22.left
        let h33 := h22.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h33
    case inr h34 =>
      -- Conjunctions on the left can always be decomposed.
      let h35 := h22.left
      let h36 := h22.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54163760296967069201981755605 : (((p5 → (p4 → ((p4 ∧ p4) → ((False ∨ p5) ∨ p3)))) → ((p1 → ((False → ((False → p3) ∧ (p4 ∧ p5))) → (p1 ∧ p5))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46858002521828230246492619756 : ((((p1 ∧ (p2 ∧ (p2 ∨ (((((p3 ∨ p4) → (p4 ∨ p3)) → (False ∧ (p3 → p4))) → True) ∧ (p4 → False))))) ∧ p3) ∨ (True ∨ p2)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747144490619708144165002281999 : ((((p5 ∨ True) → ((p1 ∧ p2) ∧ ((((p5 → p5) ∨ (p4 → (p2 ∧ (p4 → p4)))) → ((p5 ∨ p4) → p2)) ∨ ((True ∨ p2) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214762717210827727500231381313 : (((p5 ∧ p4) ∨ (p4 ∨ p3)) ∨ ((p1 ∨ (p1 → (True ∧ ((True ∨ (((False ∨ p4) ∧ p1) ∧ p5)) ∨ ((p4 → p4) ∧ p2))))) ∨ (p3 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254455780716372696367361583135 : ((p3 ∧ True) → ((p2 → ((p3 → ((p5 ∨ ((p4 → p1) ∧ True)) ∧ True)) ∧ ((((p2 ∨ p5) ∧ (p4 ∨ False)) → (p1 ∨ p4)) → p5))) ∨ True)) := by
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
theorem thm_5_vars_178519082655994399746624410228 : ((((((False → True) ∧ p5) → (p4 ∧ p3)) → p1) → (p1 → (p1 ∨ p1))) ∨ ((((p5 ∨ (p5 → True)) ∨ p3) ∨ p1) → ((False → True) ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158946643865320109743422102395 : ((p2 ∨ ((((True ∧ (True → p4)) ∨ p5) ∧ True) ∨ (((p2 → p3) → (True ∧ p4)) → (p3 ∨ p4)))) ∨ ((True ∨ ((p4 ∧ p3) → p2)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62860810290248826858298118424 : ((p4 ∧ (((True ∧ False) ∧ p4) ∧ ((p1 ∧ (p5 → (((p5 ∧ ((p1 → True) ∨ True)) ∧ (p2 ∧ p1)) ∧ p4))) ∨ (p5 ∧ (False → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215286884914476283015324002982 : ((p1 ∧ ((True ∨ p2) ∧ p5)) ∨ (((p4 ∨ (p1 → (((p4 ∧ ((False → (p1 ∧ p2)) ∧ p4)) → p4) ∧ ((p4 ∨ p4) ∨ False)))) ∨ True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341905149281542340277587871581 : (p2 → (((p2 → (((p5 ∧ ((p1 ∧ (p1 ∨ ((p3 ∧ (False → (p1 ∨ p4))) ∨ False))) ∨ False)) ∨ False) → False)) ∨ True) ∧ ((False ∧ True) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103280412494305542089387348877 : (((False ∨ ((p1 ∨ ((p3 ∨ ((p3 ∨ p3) ∧ ((True ∨ ((True → (p2 → p5)) → (p5 ∨ p2))) → p3))) ∨ p1)) ∨ True)) ∨ p4) ∧ (False ∨ True)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186277676461227939418027278676 : ((((p5 ∨ (False ∨ (((p1 → p5) ∧ True) → p3))) ∨ True) → p5) → (((p3 → p5) ∨ (True ∨ (((p1 ∨ False) → p1) ∨ (p2 ∧ p2)))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45915368556488568813053220871 : (((p4 → (((p5 ∧ (True ∨ (p3 ∨ True))) ∨ (p3 ∨ p5)) → ((p1 → ((p3 → p2) ∧ (True ∨ (False → (p2 ∧ True))))) → p3))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18069431210104808871414205646 : (((p5 ∧ (((p4 ∧ ((p2 ∨ (False ∧ True)) ∨ (p2 → (p2 ∧ p3)))) ∧ p1) ∨ (p5 ∨ (True ∧ p4)))) ∨ (p3 ∨ ((p5 ∨ p5) → p5))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115080319795756390310500882196 : (((p2 ∧ (((p5 ∧ p3) ∨ p5) ∧ ((p5 ∨ p4) → (p3 ∨ p4)))) ∨ ((((True ∧ p4) ∧ (p4 ∨ p1)) ∧ False) → (True → p5))) ∨ (p3 ∧ p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219701197322589849779995210400 : ((p1 → ((p3 → p3) ∨ True)) → ((p2 ∨ ((((p2 → (p4 ∨ (p3 ∨ False))) ∨ (False → (p5 ∧ (True ∨ p4)))) ∨ p5) ∧ True)) ∨ (p2 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678563180502987574008471293603 : ((((((p4 ∨ p4) ∨ p2) → (((p1 ∨ True) → p1) → ((p1 → False) ∧ (p2 ∨ ((p4 ∧ p4) → p4))))) ∨ (True ∧ (p2 ∨ (p4 → p4)))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176936913421012926045845405054 : (((p2 → p2) ∨ (p5 ∨ ((((p2 → (p1 → p5)) ∨ p4) ∧ p4) ∧ p3))) ∧ (p5 ∨ ((p5 ∧ ((p5 → p3) ∧ ((p5 → True) → p4))) ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53346426063457670556428040966 : ((((p1 ∨ (p2 ∨ (p5 ∨ ((p1 → (p4 → p4)) ∨ p5)))) ∧ p4) → ((p2 ∧ p4) ∨ ((False ∨ (p5 ∧ (False ∨ p2))) ∨ (p5 → True)))) ∨ p2) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h7
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h13
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h15
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52267095477082451952199984169 : (((True → (((p2 ∨ (((p3 → p5) ∧ p3) → (p3 ∧ (p5 ∧ p2)))) ∧ p3) ∧ p4)) → (p2 ∨ (((p5 ∨ p1) ∧ True) → (False ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301049407873731958973321422234 : (False ∨ ((((False → (True → p2)) ∨ ((p2 ∧ p3) → p1)) → p3) ∨ ((p5 ∨ (p1 ∨ ((((False ∧ p1) ∧ p1) ∧ False) → True))) ∨ (p4 ∨ True)))) := by
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
theorem thm_5_vars_476573305261690653648126733672 : (((((p5 ∨ p4) ∨ (p4 ∨ (p5 ∧ ((False ∧ p4) → p1)))) ∨ ((((p3 → False) ∨ p4) ∧ (p4 ∧ p1)) ∨ (True ∨ (p3 ∧ (False ∧ p4))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345868815038117878626756178062 : (p3 → ((((p5 ∨ (p1 ∨ (True ∧ ((False ∨ p2) ∨ (p4 ∨ (p3 ∨ (p3 → (((False → False) → p4) ∨ p1)))))))) → p2) ∨ (p2 ∨ False)) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (p5 ∨ (p1 ∨ (True ∧ ((False ∨ p2) ∨ (p4 ∨ (p3 ∨ (p3 → (((False → False) → p4) ∨ p1)))))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241593188074426647303856580564 : ((False → p4) ∧ (((p5 ∨ p1) ∨ (p2 ∨ ((False ∨ ((False ∧ (p1 → (p1 ∧ p4))) → (p3 ∧ (p1 ∧ False)))) ∧ p1))) ∨ (p1 → (p2 → p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251992681841329850170735973407 : ((p4 → False) ∨ ((True ∧ (True ∧ p3)) ∨ ((p3 ∨ ((p1 → (False ∧ (((p5 ∨ (True → p2)) ∨ (p2 → p4)) ∧ p1))) → p1)) ∨ (p4 ∨ True)))) := by
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
theorem thm_5_vars_46985362808087796075426379631 : ((((((p3 → True) → (p2 ∨ (p4 ∨ (((p2 ∨ p4) ∨ p2) → (p4 ∧ (p5 → p4)))))) → (p5 → (p2 ∨ p3))) → p4) ∨ (p3 ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49301651137489183881199783521 : (((False ∨ (((False → p3) ∨ True) → (p1 ∨ ((p5 ∨ p2) ∧ ((p1 ∨ p1) → (((False ∨ p2) ∧ False) ∧ False)))))) ∨ ((p4 ∨ False) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115342477696570291969629685376 : (((True → (False ∧ (((True → True) ∨ True) ∨ (p1 ∨ p4)))) → ((((True ∧ p1) ∨ (p3 ∧ p1)) ∧ (False ∨ False)) ∨ (p4 → p2))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_573823184665141686677422880139 : (((p2 → ((((p5 ∧ p5) → p2) ∧ (p1 ∨ ((((p5 → ((False ∧ ((p4 → p4) ∨ p3)) ∧ p3)) ∧ False) ∨ (p3 ∨ True)) ∨ True))) ∨ p5)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1
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
theorem thm_5_vars_157067890002975009596903876759 : (((False ∨ (((True → (p5 → (False → (p2 ∧ ((p2 ∧ p3) ∨ (p3 ∧ True)))))) ∧ False) ∧ p1)) ∨ p3) ∨ ((p1 ∧ p2) → (False ∨ (p1 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689529327327450976482673241979 : (((((((p3 ∨ p4) ∨ ((p5 ∧ False) ∨ p3)) ∨ p1) ∨ (True ∨ ((p2 ∧ True) ∨ p5))) ∨ ((p5 ∨ ((False ∧ (True → p3)) ∧ True)) → False)) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55303027583306995852553537352 : (((p5 ∧ ((p2 ∨ (True ∨ p5)) ∨ p4)) ∨ ((p5 ∨ (p5 ∧ (p3 ∨ p1))) ∨ ((p2 → (p4 ∨ (p1 → (True ∨ p5)))) ∨ (p5 ∧ False)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342794580216004856769416873215 : (p2 → (((True ∨ p3) → (((p1 → True) ∧ False) ∧ p3)) → ((p3 → ((((((p1 ∨ p5) ∨ p3) ∧ (p5 ∧ p3)) ∧ p3) ∨ p5) → False)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147231609204921329900989215856 : (((((((((p3 → ((p5 ∧ (False ∧ False)) ∧ True)) ∨ p2) → p5) → (p1 ∨ True)) → p1) ∨ p2) ∧ p3) ∨ True) ∨ (((p2 ∧ p4) → p3) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610761548432751499262455488337 : ((((((((p2 ∨ ((p4 ∨ p2) → p2)) → (p3 → (p1 ∧ False))) → ((p2 ∧ True) → p3)) ∧ ((p4 → (True → p5)) → p1)) → p2) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626655587262273850608620843578 : ((((p4 → (p2 → ((True → ((p4 → True) ∧ ((False ∧ p5) ∨ (((p5 ∨ True) ∨ ((p1 ∧ (p2 → p4)) ∨ p5)) ∧ p3)))) ∧ True))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207090573194522090377059962646 : (((True ∨ ((p4 → p1) ∨ p4)) ∧ p5) → ((p3 ∧ True) ∨ (((p1 → p4) ∧ ((p4 → p1) → p3)) → ((p5 ∧ (p4 ∨ True)) ∨ (p3 ∨ p5))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57875198824690904589230642113 : (((p1 ∨ (p5 ∨ p4)) → (p1 ∨ (p4 ∧ ((((p1 ∨ p1) → (p5 ∧ p5)) ∧ (True ∨ ((False ∧ True) ∨ p1))) → ((p2 ∨ p2) → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40588681681851795025343555299 : ((((((p2 → (True → True)) ∨ (((((((p5 ∧ p4) ∨ (True ∨ p5)) ∧ False) ∨ p1) → p3) ∨ p5) ∨ (False ∧ p2))) ∧ p5) → False) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348203382554592544582383751551 : (p3 → ((False → p2) → (((p3 → False) → p5) → ((p5 → (p4 ∧ ((p5 ∧ (p2 ∧ p2)) ∧ p2))) ∨ ((p1 → (p1 ∨ p4)) ∧ (p5 → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38442741170871707373370133383 : ((((p1 ∧ (p3 ∨ (((p1 → True) ∧ (False ∨ ((p3 → p1) ∧ False))) ∧ p4))) ∨ (p4 → ((p4 → p1) ∨ ((p2 ∨ p3) → p3)))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311196569617070531815108992304 : (p2 ∨ ((p3 ∨ p2) → ((False ∨ p3) → ((True ∨ False) → (((p3 ∨ p5) ∨ p1) ∧ (((p2 ∧ p5) ∨ ((p3 → p2) ∧ p3)) ∨ (p3 → True))))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313145553211386535846145561230 : (p3 ∨ ((((False ∧ (((p4 ∧ True) ∧ (p5 ∧ p4)) ∧ p3)) ∧ (True ∧ (p1 → p2))) ∧ (((p4 → p2) ∨ (p2 → False)) → (p4 ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314644627419986582088824522770 : (p3 ∨ ((((((False ∧ (p4 ∧ False)) ∧ (p1 → (False → (True → p5)))) → p5) ∨ p4) → p5) ∨ ((p4 ∨ True) ∨ (p4 ∧ ((p5 ∧ p3) → p1))))) := by
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
theorem thm_5_vars_53306800591312968901609829233 : (((p5 ∨ ((p5 → True) ∧ ((p5 → (p4 ∧ (p5 ∨ p5))) ∧ False))) ∨ (True → (p1 → (((p2 ∧ (False ∨ p1)) ∧ p2) ∨ (p2 → p2))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213586656893178529171372741965 : ((((False → False) ∧ p5) ∨ p2) ∨ (p4 → (p4 ∧ ((p5 ∧ (p3 ∨ (((p5 → (p5 ∧ (p4 ∧ p2))) → p3) ∧ (p4 ∧ (True → p2))))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143946235861865058707076103026 : ((((p5 ∨ ((p1 ∨ p4) ∧ p1)) → (p3 ∨ (((p1 → ((p5 → p5) → p2)) ∨ p1) ∨ (True → p4)))) ∨ True) ∧ (((p4 → True) ∨ p1) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134580442774416709430611466782 : ((((((p3 ∧ (p2 ∧ ((True ∧ (True ∧ (p4 ∧ True))) → ((p4 → p3) → p2)))) ∨ p3) ∨ False) ∨ (p1 ∨ p2)) → p1) ∨ (p5 ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244031465306062703687558544829 : ((True ∧ p2) ∨ (((((p5 ∧ p1) → p3) ∧ (p4 ∨ True)) ∨ False) ∨ ((((p5 ∨ ((p3 ∧ False) → p1)) → False) ∧ True) → (p5 ∧ (p1 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p5 ∨ ((p3 ∧ False) → p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h4
  -- False on the left can always be used.
  apply False.elim h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h12 : (p5 ∨ ((p3 ∧ False) → p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- False on the left can always be used.
    apply False.elim h15
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h16 := h10 h12
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183508666587560833703934101223 : ((p4 ∨ (((p2 ∨ (p5 → (p1 → p4))) ∨ p2) ∨ (p5 ∨ True))) ∧ ((p2 ∨ (False → (((p3 → True) ∧ ((True ∧ False) ∧ p2)) ∨ p5))) ∨ p3)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354740616924245326173251110859 : (p5 → (((p1 → (True → (((False ∧ True) ∧ (p4 ∨ p1)) → ((p3 ∨ (True ∨ p1)) ∧ (False ∧ False))))) → (p3 ∨ ((p2 ∨ False) ∧ p1))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185568513069155824837082225470 : ((p4 ∨ (p4 ∧ ((((p2 ∧ False) → p5) → p4) → (False ∧ p2)))) ∨ ((p3 ∨ False) → (((((p1 → True) ∨ p5) ∨ (p3 → p5)) → p2) ∨ True))) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159414144987270255830953308722 : ((((p5 → ((((((p3 → p2) ∧ p5) → False) ∧ False) ∨ (True ∨ p2)) ∧ (p1 ∨ p1))) → True) ∧ p2) → ((True ∧ ((True → p1) ∧ p2)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244780847375514145410591604522 : ((p1 ∧ False) ∨ (p3 ∨ ((((((False → True) ∨ p1) ∧ p3) ∧ (p5 → ((p3 → (p5 ∧ (p4 ∧ p2))) → p2))) ∨ ((p5 → p5) ∨ p2)) ∨ p3))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610026065503347110396313183236 : (((((((((p2 → p1) → (False → (p5 → False))) ∨ ((True ∧ (p2 → ((True ∧ False) ∨ False))) ∧ p5)) ∧ (p1 → False)) ∧ True) → p4) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135762867653514238413633370247 : (((True → (p5 ∨ ((p1 ∨ (p5 ∧ (True ∨ (p1 ∨ (p1 → p1))))) ∧ p1))) ∨ ((((p5 ∨ False) ∧ p5) → False) → p5)) ∨ (p4 ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41318843126967490556217809273 : ((((((False ∨ False) → p1) ∨ ((((p4 ∧ p4) ∨ (p4 ∧ p5)) → (p3 → p1)) ∨ p2)) ∧ (p2 ∧ ((p4 ∧ p4) ∧ (True ∧ False)))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198677589681235202861040632765 : ((p4 ∨ ((p1 ∧ (p1 ∧ p3)) ∧ (p3 → p3))) ∨ ((p3 ∧ (((p4 → p1) ∨ p5) ∧ p3)) ∨ ((True ∨ ((True → p3) → p4)) ∨ (True ∧ p3)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50156791788224283672497075732 : (((p3 → ((((((p3 → False) ∨ (p5 ∨ p3)) ∧ (True → (p4 ∨ False))) ∨ False) ∨ p3) ∨ (p1 ∧ p4))) ∧ (p4 ∨ ((p4 ∧ p5) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147520847020477399975462858948 : (((p5 ∨ (((True ∨ p4) ∧ (p2 ∧ ((p2 ∨ (p3 ∨ ((p2 ∨ p4) → p4))) → False))) ∨ (p3 ∧ p2))) ∨ p1) ∨ (p3 → ((p2 → p2) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157884334116734084842475135678 : ((((p1 ∨ p4) ∨ ((((p2 ∧ False) ∨ p1) → True) → p3)) ∨ (((True ∨ (p1 ∨ p4)) → p4) ∨ True)) ∨ ((p2 ∧ p3) ∧ ((p5 ∧ False) → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339674066236048289593373694359 : (p1 → (p3 ∨ (((False ∨ p2) ∨ ((p4 ∨ p5) ∨ (((((p4 ∨ p5) ∨ p3) ∧ False) → p3) ∧ (True → ((p4 ∨ p1) ∧ p1))))) ∧ (False ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60038624387938587781102254731 : (((p1 ∨ p4) → (((True ∧ p3) → ((False → (p2 ∨ (True → p1))) ∧ p5)) → ((False ∨ ((p5 ∨ ((p5 ∨ p4) ∧ False)) ∨ p4)) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697627645031607206201800066041 : ((((p3 ∨ (((((p1 → p2) ∨ p1) ∧ (p3 → p4)) ∨ False) → p1)) ∧ (True → (True ∧ ((False ∨ (p2 ∧ ((p2 ∨ p2) ∨ False))) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42241510903701691907359286665 : (((False ∧ (p4 ∧ ((p4 ∧ p3) ∨ (True ∨ (((((p1 → (p4 ∧ False)) ∧ p4) → (p2 ∨ False)) → (p2 ∨ (True ∨ p5))) → p3))))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301250065305019064567995551524 : (False ∨ ((((p2 → p1) ∨ p2) ∧ (p5 ∧ True)) ∨ ((p3 ∨ ((((((p4 ∨ p4) → p3) → p4) ∨ (p5 ∧ p4)) ∨ True) ∨ p4)) ∨ (p3 ∨ p4)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14681541323051718447559817744 : (((((p1 ∨ ((p2 ∧ p4) ∧ (True → False))) ∨ ((p1 ∧ p1) → (p2 ∧ ((p5 ∨ p2) → (False ∧ True))))) ∧ (True ∧ False)) ∨ (False → False)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119128453841041812606069475782 : ((p1 → (p5 ∧ (False ∨ ((p3 ∧ ((p1 ∧ (p4 ∨ (p2 → (p4 → ((p1 → (p2 ∨ p4)) ∧ (p4 ∧ False)))))) ∨ True)) ∨ p4)))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612554893126110385758311629709 : (((((((((p5 ∨ ((p3 ∧ p3) → ((p4 ∨ (True ∧ p5)) → p4))) → p1) → ((p5 ∨ p3) → p1)) → p2) → p2) ∨ (p3 ∨ False)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_69048356509558542204630586032 : ((p5 → (((p3 ∨ p4) ∨ (p3 → (True → ((((p4 ∧ (p4 → False)) ∨ (False ∨ (p5 → p2))) ∨ (p4 ∧ True)) ∨ (p2 ∨ True))))) ∨ p1)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777031871500015454790103591955 : (((p1 ∨ (((((p4 → False) ∨ (p5 ∨ p5)) ∧ ((((p5 ∧ (p4 ∧ True)) ∧ True) → p4) ∧ (p3 ∨ p5))) ∧ (p5 ∧ False)) ∨ (True ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



