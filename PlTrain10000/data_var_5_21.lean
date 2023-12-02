variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149255370372750521085193544398 : (((p3 ∨ p1) ∨ (p1 → (False ∨ (p5 ∧ (p5 ∧ ((((p3 → (True ∧ p5)) → p4) → (False → p3)) ∨ p5)))))) ∨ (((False ∧ p2) ∧ p2) → p1)) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147896299599413348431790896708 : ((((((p4 ∨ p5) ∨ p5) ∨ (((p2 ∧ (False ∧ p2)) ∧ (False → (False → False))) ∨ p1)) ∨ p5) ∧ (True → p2)) ∨ (False → ((p5 → p3) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45933810654583744647692262745 : (((p4 → (p5 → (p4 → ((False ∨ (p2 → ((p4 ∧ p3) → ((False ∨ p4) ∧ ((p4 → ((p2 ∧ p5) ∧ True)) → p4))))) ∨ p1)))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233634351165589728735935963472 : ((p2 ∨ (True ∨ p4)) → ((((False ∧ (p5 → (True ∨ (p1 → ((((((p2 → True) ∨ p2) ∧ p1) → p1) ∨ True) ∨ p5))))) ∧ True) ∧ p1) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256832260684567532819904642556 : ((p1 ∨ p3) → (((p4 ∧ ((False ∧ (False ∧ ((p5 ∨ (p1 → (False → p3))) ∨ (True → (True ∧ False))))) → p1)) → (p3 ∧ p4)) ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204700046655862945871443315656 : (((p4 ∨ ((p1 ∨ p1) ∧ False)) ∨ p2) ∨ ((True ∨ ((p2 → p3) ∨ p4)) ∨ (((((p4 ∧ True) → True) ∨ False) ∨ (p1 ∨ (p3 ∨ False))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112017789677169166383396193882 : (((((p1 ∨ True) ∨ p5) ∧ ((((((p1 ∧ (p1 ∧ p1)) ∧ p5) ∨ p3) → (p2 ∨ True)) ∧ p3) ∨ (p4 → (p2 ∧ p3)))) ∨ p3) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244970510203067597263520479474 : ((p1 ∧ p3) ∨ (p5 → (((p1 ∧ p5) ∨ ((((False → p3) → True) ∨ (p3 ∨ (p3 ∨ False))) → (p2 ∧ p2))) → (((False → p3) → p3) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : (False → p3) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h7
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : (False → p3) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- False on the left can always be used.
      apply False.elim h12
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h11
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65640403178090937963345892126 : ((p4 ∨ (((p3 ∧ (p4 ∧ (p5 ∨ (((p4 → p3) ∨ False) → p1)))) ∨ (((p4 ∧ p3) → (((True → p3) ∧ p2) ∧ p5)) ∨ p3)) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745114909115084192177376147565 : ((((p4 ∧ p4) → ((p3 ∨ (False ∨ (p4 ∧ (((((p2 ∨ False) ∨ (True ∨ (p3 ∧ p3))) ∧ False) ∨ (p3 → True)) ∨ (True → p2))))) ∧ p4)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60178008434180297302411799491 : (((p5 ∨ p1) → (((p4 → (False → False)) → ((p2 ∧ (p4 ∨ (False ∧ p1))) ∧ ((p2 → (p2 ∨ (p5 ∨ p4))) ∨ False))) ∧ (p4 ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180659717286210380387927874021 : (((False → ((p4 ∧ p5) → (p3 ∧ p5))) ∨ (False ∨ ((p4 → p2) ∨ True))) → ((True ∨ p5) → (((((p1 → p4) ∨ False) ∨ False) ∧ p2) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h9 =>
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- False on the left can always be used.
            apply False.elim h11
          case inr h12 =>
            -- Disjunctions on the left can always be decomposed.
            cases h12
            case inl h13 =>
              -- One of the premise coincides with the conclusion.
              exact h5
            case inr h14 =>
              -- One of the premise coincides with the conclusion.
              exact h5
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h16 =>
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
            -- False on the left can always be used.
            apply False.elim h18
          case inr h19 =>
            -- Disjunctions on the left can always be decomposed.
            cases h19
            case inl h20 =>
              -- One of the premise coincides with the conclusion.
              exact h5
            case inr h21 =>
              -- One of the premise coincides with the conclusion.
              exact h5
    case inr h22 =>
      -- False on the left can always be used.
      apply False.elim h22
  case inr h23 =>
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51488040828399900652056137093 : (((((True → p3) → (p3 → p4)) ∧ ((True ∧ (((p4 ∧ p2) → (p3 ∧ True)) → p5)) ∧ p1)) → (((p5 ∧ p3) ∧ (True → p5)) → p3)) ∨ False) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148965600715548089200447613916 : ((((p3 → True) ∨ p3) ∧ ((p1 ∨ (((p5 ∨ p4) ∨ (True ∧ True)) → (p1 → (False ∨ (p1 → p3))))) ∨ False)) ∨ (p5 → (p5 ∧ (p5 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614042675005119956565720203775 : ((((((False → p3) → ((p3 ∨ p4) ∨ ((p4 → (p4 → (True ∧ (p2 ∧ ((p1 ∨ p3) ∨ p4))))) ∨ p4))) ∨ (p2 → (p3 ∨ p3))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_56190993529986008612364830153 : (((p4 ∧ (p5 → (p2 → True))) ∨ (p2 → ((p4 → (p1 ∧ p2)) → (p1 → ((True ∧ (p4 ∧ ((True → p2) → p5))) ∨ (p4 ∧ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348971444336783657470485382528 : (p3 → (p4 ∨ ((((p1 ∧ p1) → (p4 → (p5 ∨ ((p4 → p2) ∨ p5)))) → (((False ∧ (p5 ∨ (p3 ∧ p2))) ∨ (p2 ∧ p4)) ∨ True)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234061996645491112009842013643 : ((p5 ∨ (p5 → p4)) → ((p4 ∧ ((p2 ∧ (p4 ∧ ((p4 ∧ (p5 ∧ p4)) → (p2 → True)))) → p1)) ∨ (True ∨ ((False ∨ (p3 ∨ p4)) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111149485772838324369375263355 : ((((((p2 → p4) → p1) ∨ (True ∧ p2)) ∨ (((p4 → (p1 ∧ False)) ∨ (p3 ∨ (p4 ∨ p3))) ∨ (p1 ∧ (p5 → False)))) ∧ p1) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596375482301805284755207237287 : ((((((p2 ∧ (p3 → p2)) ∨ ((p4 ∧ True) ∧ p3)) ∨ ((p4 ∨ p3) ∨ (((True ∧ p2) ∧ (p5 ∨ (p4 → (p1 → p1)))) ∧ p5))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54608396377650846293789509045 : (((p3 → (((True → (p1 ∨ True)) ∨ p2) → False)) ∨ (((p2 ∨ False) ∧ (p5 ∨ ((p5 ∨ True) ∧ (((p2 → p2) ∨ p5) ∨ p3)))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196736031342363804626050759334 : ((((p2 → ((False ∨ p2) ∧ p2)) → False) ∧ False) ∨ (((((False ∧ p2) ∧ (False → p5)) ∧ p3) ∧ p4) → (p2 ∨ (False ∧ (False ∧ (p4 ∨ p3)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192605772205951626565155683788 : (((((((p5 ∧ p2) ∧ True) ∨ True) ∨ p3) ∧ p1) → p4) → ((((p3 → (((p1 ∨ (True ∧ p3)) → (True ∧ p5)) ∧ p3)) → p4) ∧ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611317159327310922788104205627 : ((((((p1 ∧ p4) → ((p5 ∨ ((p2 ∧ ((p4 ∧ p2) ∧ (True ∧ (((p1 ∨ (p3 ∧ p3)) → p3) → False)))) ∨ p1)) → p3)) → p5) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782104351919576600267407466251 : (((p3 ∨ (((p2 ∨ (((p2 → p5) ∧ (((p2 → p2) → p1) → (((p3 ∨ p3) ∧ (p5 ∧ True)) → (p3 → False)))) ∧ True)) ∨ p2) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135383296047736244343184069393 : (((((p2 → (((p4 → (p4 ∨ p3)) → False) ∧ (False ∧ p4))) ∨ (p1 → (True ∧ p4))) → p1) ∨ ((False ∧ p2) → True)) ∨ ((p5 ∨ p3) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55753697305589295445854457470 : ((((p5 ∨ (p1 → p2)) → False) ∧ ((((p3 ∨ ((p1 ∧ p1) ∨ p3)) ∨ (True ∧ p5)) ∨ ((p1 ∨ True) ∧ p2)) ∧ ((p3 ∨ False) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118530682637917971818119811249 : ((p3 ∨ (p1 ∧ ((False ∧ (((p3 → (True ∨ (p2 → (True ∨ p5)))) ∨ (True → ((True ∨ True) ∧ (p4 → False)))) → p1)) ∨ True))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153748333182243793104082760710 : ((p3 → (p2 → (((((True ∨ p3) → False) ∨ (p5 ∨ p5)) ∧ (p3 ∧ (True ∨ ((True ∧ p4) ∨ p2)))) ∧ False))) → ((p3 ∧ (p2 ∧ p3)) → p4)) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53395494670029635751781750058 : ((((((p2 → False) ∨ False) → ((False ∨ p3) → p1)) ∧ (p3 → p5)) → ((p3 → p1) ∧ (p5 → (((p5 → p1) ∨ False) ∨ (True → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_914990665939443702936916181670 : ((((p4 ∧ (((p4 ∨ (p3 ∨ p5)) ∧ (p4 ∧ (p2 ∨ False))) → (False ∧ (p5 → p1)))) ∧ (p2 ∧ (False → (False ∧ (p2 → (False ∧ p5)))))) → False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h8 : ((p4 ∨ (p3 ∨ p5)) ∧ (p4 ∧ (p2 ∨ False))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187217292014693522771942307423 : (((False → p5) → (True ∨ ((((True ∨ p1) ∧ p5) → False) ∨ p4))) → (((True ∨ True) → True) → ((((True → p5) → p2) → p5) ∨ (True ∨ False)))) := by
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
theorem thm_5_vars_115934342452997592164831261718 : (((p3 ∧ (True → (p5 → True))) ∨ ((((True ∨ p2) ∧ True) ∨ p3) ∧ ((p2 ∨ p1) ∨ ((p3 ∧ (False ∧ (p1 ∨ p4))) ∧ False)))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38627895212160127166888942536 : ((((((p3 ∨ p2) → (p1 ∧ True)) ∨ (p5 ∧ False)) ∨ ((p2 → (p4 ∧ (p3 ∨ (p2 → p4)))) ∨ (p4 ∨ ((p2 ∧ p5) ∧ p1)))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25563224973360034535738497040 : (((True → (p1 ∧ p5)) → (((p1 ∨ p5) → ((p3 ∨ (((((p4 ∧ p4) ∨ p4) ∨ ((p1 ∧ p1) ∨ p4)) → p3) → False)) ∧ p1)) ∨ p5)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157906038199299127901071970768 : ((((False ∨ (p3 ∧ (True → (p4 ∧ p4)))) ∨ (False ∨ p5)) → ((((False → p2) → p5) ∨ p1) ∧ p1)) ∨ ((True → False) → ((p1 ∧ p4) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177722567656027619008315049757 : (((((p3 → (False ∨ p2)) → p3) ∧ (p4 ∨ (p4 ∧ (p3 ∧ p5)))) ∧ p1) ∨ (p2 → (((p1 → (False → p1)) ∧ p5) ∨ (p2 ∨ (True ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156867682292408759511048836389 : (((((p3 ∨ (p3 ∨ p2)) ∧ (p4 → (True ∧ ((p4 ∧ p4) → ((True → False) ∨ p2))))) ∧ p2) ∨ p2) ∨ (True ∨ (p3 ∧ (p4 ∧ (p3 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347606896177704468162876184618 : (p3 → (((True ∧ p3) ∧ (False ∧ p5)) ∨ ((p5 → (((p2 → p3) ∧ (p5 ∨ (True → p3))) → True)) → (((p5 ∨ (p3 ∧ p5)) ∨ False) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773160666691311481279912081223 : (((False ∨ (((((p4 ∨ (((p5 ∧ ((p3 ∧ ((True → (p1 → False)) → (p3 ∨ p1))) ∨ p4)) ∨ p1) → p1)) → p4) → p3) ∨ True) ∧ True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_15436082173568970097843545943 : ((((((((p4 ∧ True) ∧ p2) → (p5 → (((p2 ∧ (p4 → p1)) → p2) ∧ (p1 ∧ p5)))) ∧ (p4 ∧ p3)) → p2) → True) → (p1 ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204700764054688979883054075069 : (((p4 ∨ ((p1 ∧ p4) ∨ p4)) ∨ p2) ∨ ((True ∨ p1) ∨ (((p4 ∨ (((p5 ∨ False) → p4) ∧ ((p1 ∧ p5) → True))) ∧ True) ∧ (p2 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116592749495068220631907957566 : (((p5 ∨ True) ∧ ((((p1 → (p1 → (p4 ∧ p2))) → ((p4 ∧ (p4 ∨ p2)) ∨ (p3 → p2))) ∧ (p5 → p3)) ∨ (p3 ∨ p1))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57243799981026014492686312062 : ((((p3 ∧ True) → p4) ∨ (((p3 ∧ (False ∨ (p4 ∨ (p1 → (p3 → (False ∨ ((p1 ∨ False) ∧ True))))))) ∨ p3) ∨ (p5 → (False ∨ True)))) ∨ p5) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246590904151007095397926984472 : ((p5 ∧ p2) ∨ ((p2 ∧ p1) ∨ (p2 ∨ ((False ∧ ((p1 → (((True ∧ ((((p4 → True) ∧ False) ∨ p5) ∨ p2)) ∨ p4) ∧ p1)) ∧ p5)) → p3)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608158460118198932068638456315 : (((((((p4 → (p4 ∨ p5)) → (((p5 ∧ (p1 ∨ p1)) ∨ ((((p4 ∨ p2) → p4) ∧ p3) ∧ p4)) ∧ (p5 ∧ p5))) ∧ p3) ∨ False) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263068022577403641833905057475 : (True ∧ ((((p3 ∨ (True ∨ ((p1 ∨ p5) ∧ (p5 ∧ (True → ((p4 ∧ (p1 ∨ p2)) → ((p2 ∧ p3) ∨ p1))))))) → p3) ∧ False) ∨ (True ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729748661193196530489262900549 : (((((p3 → p4) ∨ p4) → (((p5 → p1) → (p2 ∧ ((True ∨ (p1 ∨ (True ∧ (p2 → (p3 → p3))))) ∧ (True ∨ False)))) ∧ (p2 ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147878398792603829994017188823 : (((p5 → ((p4 → (False ∨ ((p1 → (p5 ∧ ((False → p3) → True))) ∧ (False → (p4 ∧ p3))))) ∨ p1)) → False) ∨ (True ∨ ((p1 ∧ p3) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51845471954823652458861135347 : ((((((True ∧ (p1 ∨ p4)) ∧ (False ∨ True)) ∨ (p3 ∨ ((False ∧ True) ∨ p1))) ∧ p4) ∨ (((False → (p5 ∧ p5)) ∨ (p3 ∧ True)) ∨ p5)) ∨ p5) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600768570718220989858394876325 : ((((False ∧ ((p4 → ((p5 ∧ p1) ∧ True)) → (p2 → (p3 → ((True → ((((p3 → p5) → p1) ∧ p1) ∧ p2)) ∧ (p3 → p4)))))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227839332627669041142492420345 : ((p2 ∧ (p5 ∧ False)) ∨ ((((True → (p1 → ((p2 ∧ p2) ∨ (((p5 ∨ p3) ∨ (False → ((p3 → p2) ∧ p5))) ∨ p1)))) ∧ p1) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166022007523310742818300794658 : (((p5 ∨ False) ∨ (((p4 ∧ (p3 → (True ∧ (p5 → False)))) ∨ p4) ∧ ((False ∧ False) ∨ False))) ∨ ((p4 → p4) ∨ (p2 ∧ (p1 → (True ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151178656924661766283955512612 : ((((((p2 ∧ False) → (True ∧ ((p1 ∨ p2) ∧ False))) ∧ True) ∨ ((((p2 → p5) ∧ False) → p4) ∧ False)) → p2) → (p1 ∨ ((p4 ∨ p5) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p2 ∧ False) → (True ∧ ((p1 ∨ p2) ∧ False))) ∧ True) ∨ ((((p2 → p5) ∧ False) → p4) ∧ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
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
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h9
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_467665344985980679008244886742 : (((((((p4 → p1) ∧ p5) ∧ True) ∧ ((p1 ∨ (p3 ∧ (p5 ∧ False))) ∧ p3)) ∨ ((p5 → ((p3 → p3) → (p5 ∨ (True ∧ p3)))) ∨ p3)) ∧ True) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52596498454813743299630310816 : ((((p2 ∧ (((True ∧ False) → p5) → p5)) ∧ (p4 → (p3 ∧ (p5 ∨ p5)))) ∨ ((True ∧ (p5 → ((p4 → (False → p2)) → p3))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141229377257577350185361503368 : (((((p4 ∧ (p3 → p5)) → p4) → p4) → (p4 → (((p4 → ((p4 ∧ p4) ∨ True)) ∨ (p4 → True)) ∨ (p2 ∨ p3)))) → (p5 → (p3 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64007452104148062216426506815 : ((False ∨ ((p3 ∧ ((((p2 → (((True ∧ (p5 ∧ ((False ∨ p5) ∧ p3))) ∧ p4) → (p4 ∨ True))) ∧ p4) ∨ p4) ∨ False)) ∧ (p2 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189005822046962552729326614238 : ((((p4 → True) ∨ p2) ∨ (p3 ∧ ((p1 ∧ p5) ∨ p2))) ∧ ((((((True → False) → p1) ∧ (p2 ∨ ((p4 → p5) → False))) ∧ p4) ∧ p4) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66001748556628949211438982312 : ((p4 ∨ (p5 → ((p3 ∨ ((p4 ∨ ((p1 ∨ (p2 → (((True → (p2 ∧ p2)) ∧ (p5 ∨ p4)) ∧ p1))) → p3)) → (False ∨ p3))) ∨ True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113211677555029300239030553104 : (((((p1 → True) ∧ (p5 → ((((True ∧ (p5 → (p2 → (p3 → p2)))) ∧ p2) ∧ p2) → (p2 → p3)))) ∨ True) ∧ (p2 ∨ p5)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115685841951725891597393945740 : (((p1 ∨ (p1 ∧ (True → (p2 ∧ False)))) ∨ (((p5 → (True ∧ p3)) → (p4 ∧ p1)) → (p3 → ((p1 ∧ p4) → (p2 ∧ p1))))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112519477456583930613981029030 : (((((((p4 ∧ (p1 ∧ (((p5 ∧ (p2 → p3)) → (p1 ∧ p4)) ∧ (False → p5)))) ∧ (False ∨ p1)) → p3) → False) → p5) → p4) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199428765557384631833286882754 : ((((p4 → p4) → (p1 ∧ (p2 ∧ False))) ∨ p2) → (p2 → (((p3 ∨ False) ∨ True) ∧ (p1 → ((True ∨ p5) → (p2 ∧ ((p5 ∨ p1) ∨ p5))))))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h12
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150078820517842774278433259665 : ((True → ((p4 → p3) → (p4 ∨ ((((p5 ∨ (p5 → p5)) ∨ p1) ∧ (((True → p2) ∧ p1) ∨ True)) ∨ p5)))) ∨ (p1 ∨ ((False ∨ p3) → p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233092005117280081599310238655 : ((p4 ∧ (p1 → False)) → (p2 → (((True ∧ (False ∨ (p3 → p3))) → ((p3 ∨ p5) ∨ (p3 → (False ∧ (((p3 ∧ True) ∨ True) ∨ p4))))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134994223498626710127528066536 : (((False ∧ (((((False → (False ∨ True)) → (p5 ∧ p4)) → ((False ∧ p1) ∨ (p5 ∧ p3))) ∧ p4) → False)) ∧ (p4 ∧ False)) ∨ (False → (True ∧ p3))) := by
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
theorem thm_5_vars_66480354478336610420172127928 : ((True → (((((p3 → p5) ∨ (p5 ∨ True)) → (((((False ∨ p4) ∧ False) ∨ p2) ∧ ((p2 ∧ (p4 → p4)) → p2)) ∧ p2)) → p4) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110920377428357705258975532928 : ((((True → ((p5 ∨ (((p4 → p5) → (p5 ∨ (p5 ∨ (p1 ∨ (False ∨ p1))))) ∨ (False ∧ False))) ∨ (p3 ∨ p3))) → p5) ∧ p2) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77895608789898443011241684412 : (((p1 ∨ (p1 ∨ ((p4 ∨ p2) → ((p2 ∨ (p5 ∧ p2)) ∨ ((True ∨ (((p3 ∧ False) → ((p5 ∨ True) ∨ False)) → p5)) ∨ p2))))) → False) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ (p1 ∨ ((p4 ∨ p2) → ((p2 ∨ (p5 ∧ p2)) ∨ ((True ∨ (((p3 ∧ False) → ((p5 ∨ True) ∨ False)) → p5)) ∨ p2))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4144596796425030244373458913 : (p4 ∨ (((p5 ∧ (p2 ∨ (((((True ∧ (p3 ∧ p5)) ∨ p2) → p5) ∧ p4) ∧ (((True ∧ p2) ∨ p2) → (False → p2))))) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668591765958356985751633061862 : ((((((p3 → p4) → ((True → p4) ∧ (p1 ∧ (((p5 ∧ p4) ∨ (p4 ∨ (False ∨ True))) ∨ (True ∧ p5))))) ∧ False) ∨ ((p5 → p5) ∨ False)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38510895072473887921260485138 : ((((True → (p1 ∨ (((((p2 ∧ p1) → p1) ∨ p2) ∧ True) → False))) ∨ ((p3 → (((p2 ∨ p3) → (p4 ∧ p1)) → p2)) ∨ p1)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136185784392996118798285023059 : ((((p3 ∨ (p4 → p4)) ∧ (p1 ∧ True)) ∧ ((p5 ∧ (((False → (False → p3)) ∧ p4) → (p2 ∨ (True → p1)))) ∨ p2)) ∨ ((p5 ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661694097891867097675760130086 : ((((((((p3 ∨ (((False → ((p2 ∨ p1) ∨ p4)) → p4) → p4)) ∨ False) ∧ True) ∨ p3) ∧ ((p4 ∨ p4) ∧ (False → False))) → (p2 ∨ p4)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h3.left
        let h10 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h12
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h3.left
        let h15 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h17
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h3.left
    let h21 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58158655903024800885681315984 : (((p3 ∧ True) ∧ ((p1 → (((((p2 → ((p3 ∨ False) ∨ True)) ∨ ((p3 ∨ (p5 ∨ True)) → p4)) → p2) → (p5 → p4)) ∨ False)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209397184419210766307533635448 : ((p1 → (True ∨ (True ∨ (False ∨ p5)))) → ((((p1 → ((p4 ∨ ((True ∧ p4) → (False ∧ ((p3 ∨ p5) → p2)))) ∨ False)) ∨ True) ∧ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184750868173601811153121272643 : ((((False ∧ p4) ∨ (p4 ∨ p5)) ∧ ((True ∧ (True ∧ p3)) ∨ p3)) ∨ (True ∨ ((((p5 ∧ p2) ∧ p2) → ((p1 → p3) ∧ (False → True))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192837673793767587299046155691 : ((((False → (p3 ∨ (p3 ∧ p4))) ∧ p3) ∧ (p3 → False)) → ((p4 ∨ p4) → ((True → (p5 ∨ (p5 ∧ ((False ∨ (p1 → False)) ∨ True)))) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667590878428064066846378047844 : ((((p2 ∧ (((False → (False ∧ (p5 ∧ (((p3 → (p2 ∨ ((p4 ∧ p5) → False))) → p4) ∨ p3)))) → p2) ∧ True)) ∧ (True ∨ (p2 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747917084385907419812834573169 : ((((False → p5) → ((True → (((True → p4) ∧ p3) → (((p4 → p2) ∧ (p1 ∨ ((p5 → p5) ∨ ((p1 → p4) ∧ False)))) ∨ False))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811002509035863561906115815713 : (((p5 → (True ∧ (((((((p3 → (p5 ∧ False)) → p4) ∧ (True ∨ p3)) → ((p1 → p3) → False)) → p1) → p1) ∨ ((p4 ∧ p2) ∨ p5)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230694939389813164564179388213 : (((p4 → p1) ∧ p5) → (p1 → ((False ∨ (p4 ∧ (((p3 → (True → (True ∨ p3))) → (p1 → (((False → p4) ∨ False) → p2))) ∧ p5))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190783541198977954918568853937 : ((((((False ∨ p3) ∧ False) → p5) → p4) ∨ (False ∨ False)) ∨ ((True ∧ (p2 → (True ∨ (((((p3 ∨ p5) ∨ p4) ∧ p3) → p4) ∨ p1)))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105093783792598742153199599932 : (((((p4 → (p1 → p1)) → (p3 ∨ (p2 ∧ (p1 ∧ (False ∨ (False ∨ ((True ∧ p3) ∧ False))))))) ∨ True) ∨ (True → (p4 → p5))) ∧ (p1 → p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58963588146942890299617429607 : (((p2 ∧ p2) ∨ ((p5 ∧ ((True → (p1 ∨ (((((False ∧ p1) → (p2 ∧ p1)) ∧ p1) → p5) ∧ p1))) ∧ (p3 ∨ False))) ∨ (True ∨ False))) ∨ p3) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249107935701312349827474262573 : ((p4 ∨ p2) ∨ ((((((((((False ∧ True) ∧ p1) ∧ (p5 ∧ p5)) → p5) ∨ p2) ∧ True) → ((p2 ∧ p1) → False)) ∧ p3) ∨ (True ∨ p3)) ∨ p3)) := by
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
theorem thm_5_vars_613901190536908728062945183393 : (((((((True → ((p5 ∨ p3) → p1)) ∨ ((p4 ∧ False) → ((False → p4) → (p4 → (False ∨ False))))) → p5) ∨ (True ∨ (p2 ∨ False))) ∨ p5) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_219619815440125818407785729286 : ((False → ((p2 ∨ p2) ∧ p3)) → (((p4 → (p1 ∨ (p1 → p2))) → (((((p2 → p2) → p5) → (p3 → p1)) ∧ p3) → (p1 → p3))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350004749199492265993472241559 : (p4 → (((p3 ∧ (((p3 → p2) → p1) ∧ (((p1 ∧ (((((True → True) ∨ True) → (p5 ∨ p5)) ∧ False) ∧ p4)) ∨ p3) ∨ p3))) ∨ p4) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192969327685304404760147537769 : (((p3 ∨ (p1 → (False ∧ (False ∧ True)))) ∨ (False → p4)) → (((False ∧ True) ∧ ((((p3 → p5) ∧ p5) ∨ True) ∨ (False → (p4 ∨ p1)))) ∨ True)) := by
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
theorem thm_5_vars_3419120644528518792503770227 : (True ∧ ((p1 ∧ ((((p2 → p4) ∨ p2) ∧ (False → ((p5 → (p4 → (False ∧ p2))) ∧ True))) ∧ (((p4 → False) ∧ p2) ∨ p2))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64555241297143281282210943883 : ((p1 ∨ ((p1 ∧ (True → (p2 → False))) ∨ (((((p2 → p3) → (p3 ∧ (p2 ∨ (p1 ∧ (p3 → p4))))) → p2) ∧ (p4 → p5)) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683621114649798682740821787916 : ((((((True ∨ (p1 ∧ (((p5 → p1) → (False ∨ (False ∧ p1))) → p2))) → (p4 ∧ False)) ∧ p1) ∨ (True ∨ ((p5 ∧ (False ∧ p2)) ∨ p5))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_943191924370295052659743227159 : (((((p1 ∨ True) → (p1 ∧ p5)) ∧ (False → ((p3 → (((True ∨ True) ∧ ((p4 → p1) ∧ p5)) ∨ ((p5 ∨ p3) → (False ∨ True)))) → False))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p1 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134086732050369535118629962875 : (((((p2 ∨ (True → p2)) ∨ (((False ∧ ((False ∨ p5) → (p1 ∨ False))) ∨ ((p5 → False) ∨ p5)) ∨ p1)) → False) ∨ False) ∨ ((p4 → p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84745198172492040960450192952 : ((((p2 → (p1 ∨ (True ∨ (p3 → (p5 ∧ p1))))) → (p4 ∧ (False ∧ False))) ∧ (p3 ∨ ((((p3 ∧ (False ∧ p2)) ∧ p1) → p1) ∧ p3))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p2 → (p1 ∨ (True ∨ (p3 → (p5 ∧ p1))))) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : (p2 → (p1 ∨ (True ∨ (p3 → (p5 ∧ p1))))) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h13
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- We need to get the left conjuct of h16 based on <expert-advice>.
    let h17 := h16.left
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160770283418746373689888970287 : ((((p1 → False) ∨ (False ∧ (p2 → True))) ∧ ((p1 → (True ∧ p5)) ∨ ((False ∨ (False → False)) → p5))) → (p5 → ((False ∨ (p4 ∨ p2)) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
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
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_74484425384521953451396005753 : ((((False ∨ True) → ((((p4 ∧ (((p3 ∨ (p1 ∧ True)) ∧ p5) ∧ (p3 ∧ p1))) → p3) ∨ (p3 → ((p4 ∧ p1) → True))) ∧ p2)) ∨ False) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- We need to get the right conjuct of h4 based on <expert-advice>.
    let h5 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_381624126152878686103125586830 : ((((((((False ∧ p1) ∨ p3) ∨ (p1 ∧ ((((p1 → (p4 ∧ p3)) → False) ∨ ((False → (p3 → p1)) → True)) ∨ p4))) ∧ p1) ∨ p4) ∨ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



