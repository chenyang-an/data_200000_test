variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_987425277461914876451777787702 : (((p2 ∧ (p4 ∨ ((p2 ∧ (p2 → False)) ∧ (((p1 → (True → ((((p5 → p5) ∧ p3) ∨ False) ∨ True))) ∨ ((p1 ∨ False) ∨ p1)) ∧ p2)))) → p4) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h7.left
    let h11 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h13 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h14 := h9 h13
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
          have h18 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h11
          -- We have shown the premise of h9, we can now drive its conclusion.
          let h19 := h9 h18
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- False on the left can always be used.
          apply False.elim h20
      case inr h21 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h22 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h23 := h9 h22
        -- False on the left can always be used.
        apply False.elim h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702166087746409944244713205660 : ((((p5 → (p2 ∨ (((False ∨ (False ∨ True)) ∨ p1) ∨ p5))) ∧ (p1 ∨ ((((p3 ∨ (p5 ∨ (False ∨ p1))) ∧ p5) → (p5 → True)) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41072065407739604850636354540 : ((((p5 ∨ ((p3 ∧ (p2 ∧ True)) → ((p3 ∨ ((((p1 ∧ (True ∨ True)) ∧ p3) ∧ p4) ∧ p2)) ∧ (False ∧ p2)))) → (p3 → p1)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57435927630202994492201697038 : (((p3 ∨ (p1 → p4)) ∨ (p1 → (((p1 ∨ p5) ∧ True) ∧ (((p1 ∧ True) → ((p5 → ((False → (p1 ∧ p2)) ∧ p2)) ∨ False)) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160946347588496670563195191012 : ((((p2 → p4) ∧ p2) ∧ ((((p1 ∧ ((False ∧ p1) → p4)) → ((True ∨ p5) → p5)) → p5) → False)) → ((p2 → (p4 ∨ (p5 ∨ p4))) ∨ p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117286119384508974304636675700 : ((False ∧ (((((True → True) → (p4 → p5)) → ((True → p1) → ((p3 ∨ False) ∧ ((p4 → (p5 ∨ True)) → p1)))) → p1) → False)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300535207728545001057122183094 : (False ∨ (((((((True → p2) → p5) → (((p5 ∨ (p5 ∨ True)) → p1) ∧ (False ∨ p4))) ∨ p1) ∧ False) ∨ True) ∨ ((False ∧ True) → (p4 ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735687672954903089084887822711 : ((((p5 ∨ p2) ∧ (((p4 ∧ p5) → (p1 ∧ False)) ∨ ((p3 ∨ p2) ∨ (((True ∧ p4) ∧ (p5 ∨ ((False → p4) → p3))) → (p1 ∨ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261419864342156301096146340075 : ((p5 → p1) → (p1 ∨ (p5 → ((((p4 ∨ (((False → ((p3 → p5) → (p3 ∨ False))) ∨ p5) ∨ p4)) → p2) ∨ ((False ∨ True) ∨ True)) ∨ True)))) := by
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
theorem thm_5_vars_225305508893855765226360621770 : (((False ∨ p2) ∧ p2) ∨ (p1 ∨ ((p1 ∧ (p4 → ((True ∨ (((p1 ∨ True) → ((p5 ∧ p2) → p5)) → True)) ∧ False))) ∨ (False ∨ (True ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302500627659562873247835674847 : (False ∨ (False ∨ ((p3 → ((((p4 ∨ (p3 → p4)) → p3) ∧ (p4 ∨ p1)) ∨ (((True → p4) ∧ ((False ∨ p1) ∨ p4)) ∨ (p3 ∨ p5)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111675200007500255671720712619 : ((((p4 → ((p2 ∨ (((p1 → (p2 → True)) ∨ p3) ∨ p2)) → ((p3 ∨ (((False → p4) ∧ True) → False)) ∧ p4))) ∨ True) ∨ p3) ∨ (p1 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117039133654742217925119053983 : (((p3 ∨ p2) → (False ∨ (((False ∨ (False ∧ (p4 → ((p5 → p5) ∧ p4)))) → (False → p2)) → ((p5 ∧ (p4 ∧ p1)) ∨ p2)))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190680462721599688442199449762 : (((p4 → ((p1 → ((p2 ∨ p1) ∨ p5)) ∧ p5)) → p1) ∨ ((p4 → p1) → (True ∨ (((p2 → (p3 ∨ p1)) → p5) → (True ∨ (True → p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54539060431844957224508381976 : ((((p4 ∨ p5) → (p3 ∧ ((p2 ∧ p2) ∨ p1))) ∨ (((p3 ∨ p1) → (p1 ∧ (True → p4))) ∨ (((p3 ∨ (p1 ∨ p4)) ∧ True) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118523102449522193790834703291 : ((p3 ∨ ((p5 ∨ p4) ∨ (p4 → (p3 ∨ (((p3 ∧ (p4 ∧ p1)) → p2) ∧ (p3 ∨ (False → ((p4 → (p4 ∧ p4)) ∨ p2)))))))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671264084231468199342327528967 : ((((p4 ∨ (p2 → (True ∧ ((p5 ∧ (((True ∨ True) ∨ False) → ((p1 ∨ p2) ∧ p5))) ∧ ((p3 ∧ p5) ∨ p2))))) ∨ (p3 ∨ (p5 → p5))) ∨ False) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_385308173444958219860929051093 : (((((p3 → (((False ∧ p5) → (((p5 ∧ p4) ∨ p2) ∨ True)) ∨ (p3 → (((p1 ∨ ((True → p1) ∧ True)) ∨ False) → p2)))) → p3) ∨ True) ∧ True) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783370696497836506227067693479 : (((p3 ∨ ((((p1 ∨ (p1 ∧ True)) → (p1 → ((p4 → ((p2 ∧ p3) ∧ False)) ∨ False))) → False) ∨ ((True → ((p3 ∧ True) → p1)) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586202972910463483411084621233 : ((((((((p5 ∨ p5) ∧ (p1 ∨ p1)) ∧ (False ∧ ((p4 ∨ p1) → True))) ∨ (p4 → (False ∧ ((p2 → p1) ∨ (p5 ∧ True))))) ∧ p1) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165773361920154698402739650231 : ((((p2 ∨ (p3 ∨ p5)) → False) → ((((p2 ∨ p3) ∨ ((p3 ∧ True) ∨ p3)) ∨ p5) → p4)) ∨ (((p4 → p5) ∨ True) → (p1 ∧ (p5 → p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h6 : (p2 ∨ (p3 ∨ p5)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h7 := h1 h6
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h9 : (p2 ∨ (p3 ∨ p5)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h8
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h10 := h1 h9
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h15 : (p2 ∨ (p3 ∨ p5)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h13
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h16 := h1 h15
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h18 : (p2 ∨ (p3 ∨ p5)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h17
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h19 := h1 h18
        -- False on the left can always be used.
        apply False.elim h19
  case inr h20 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h21 : (p2 ∨ (p3 ∨ p5)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h20
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h22 := h1 h21
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137789870515408523605545923871 : ((p2 ∨ (True ∧ (((((False ∨ p5) ∧ ((p4 ∨ (p1 → p4)) → (p4 ∨ (p5 ∧ p3)))) → p4) ∨ p3) ∨ (p1 ∧ p4)))) ∨ ((p4 ∧ p5) → p5)) := by
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
theorem thm_5_vars_646624051026824265562701106678 : ((((p1 → (True ∨ ((False → (p3 ∨ ((p2 ∧ (p3 ∧ p1)) ∨ (p1 ∨ p5)))) → (((True ∧ (p5 ∨ p2)) ∨ False) ∧ (p1 ∧ p2))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322295089480021071549387773521 : (p5 ∨ (((((p5 ∧ False) ∧ (p1 → (((p4 ∨ p1) ∧ p3) ∨ p2))) → (((True ∨ ((True ∧ (p5 ∨ p1)) → p1)) ∧ p3) → p5)) → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346291719458675621326412297703 : (p3 → ((((p3 ∧ (p2 ∨ (p1 → (p4 → ((p5 → ((p2 ∧ ((p3 ∨ (p4 ∨ p5)) ∧ p4)) ∧ p4)) → p2))))) ∧ p5) ∨ p3) ∨ (p3 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40155965620007438820356141460 : (((((p5 ∨ ((p1 ∧ ((False ∨ p1) ∧ p2)) ∨ ((p5 ∧ p4) → p2))) → ((p3 ∨ (p2 → p4)) → (p4 → (p1 ∧ p5)))) ∧ False) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801292920070799729720492709378 : (((p2 → ((((p5 ∨ False) ∧ (p5 ∨ ((p1 ∨ (p4 → (p2 ∨ False))) ∧ p1))) ∧ p2) ∨ ((p4 ∨ True) ∨ ((True ∨ (p5 ∧ p4)) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39075474073022666369043155321 : ((((p1 ∨ p2) ∨ ((((((p2 ∧ (p3 ∨ (p1 ∧ True))) → p5) ∨ (p1 ∧ p1)) ∨ (p3 ∧ (p1 → (p2 ∧ p3)))) ∨ p5) ∨ False)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114168832411383101482288029751 : ((((p5 → ((((p2 ∨ ((p3 ∨ p2) ∧ (p3 → (True ∨ p3)))) → p5) → (p2 ∧ p5)) ∧ p4)) → p1) → (False ∧ (False ∧ True))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111286763548991054987673996999 : ((((p1 → p5) → ((p3 → ((True → p1) ∧ (p5 ∧ ((p2 ∧ (p4 ∨ False)) → p3)))) → ((True → (p5 ∨ p3)) ∨ p2))) ∧ False) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165317365543444712813222135469 : (((False → (((p4 ∧ p4) → ((True ∨ True) ∨ False)) ∨ ((p2 ∧ p2) → p4))) → (p5 → p1)) ∨ ((p1 ∨ (True ∨ True)) → ((p3 ∧ p4) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158651195506039398056772274691 : ((p1 ∧ ((p3 → (p1 ∨ False)) ∨ (p2 ∨ (True ∧ ((((p1 ∨ True) ∨ True) → (p3 ∧ p1)) ∧ p2))))) ∨ (p4 → (((p1 ∨ p3) → True) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228161954147885623712202419329 : ((p5 ∧ (True ∧ p2)) ∨ (True ∧ (((p4 ∨ ((p5 ∧ (((p2 ∧ p1) → p4) ∨ (p4 ∧ p4))) ∧ (p1 ∧ p1))) ∨ ((p3 → p1) ∧ False)) ∨ True))) := by
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
theorem thm_5_vars_204280273026149059097533391363 : ((((p3 ∧ True) → (p4 → False)) ∧ p3) ∨ (((p4 ∧ (((((p2 ∧ (p4 ∨ p3)) → False) ∨ p5) ∨ ((p5 → p3) → p2)) ∧ False)) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53243359799205414944207213961 : (((((p3 ∨ p3) → p1) → (((True → False) ∨ (p2 ∨ False)) → p5)) ∨ (False → (p3 ∨ (True ∧ (p3 ∨ (((False ∧ p3) ∨ p5) → True)))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_36749195183614456203427467078 : ((p5 → ((p1 → (((((p3 ∧ (((p4 → (True → p1)) → p3) ∧ False)) → p4) ∧ ((p4 → p2) → p3)) ∨ False) ∨ True)) ∧ (False ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
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
theorem thm_5_vars_48975480357059940196414753423 : (((((p2 → (((((p1 ∨ p5) ∨ False) ∨ ((p2 ∨ (p2 ∨ p5)) ∨ p4)) ∨ p1) ∧ p2)) → (False ∨ p2)) ∨ p5) ∨ ((p2 ∧ p3) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303863811353557695639029026333 : (p1 ∨ ((((p2 ∨ (False → (p3 ∨ (((p1 ∧ p1) ∧ ((p5 ∧ False) → (p3 ∨ p5))) ∧ p3)))) → (False ∧ p5)) ∨ (p3 → (p1 → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42325747637148811571601459195 : (((p2 ∧ (p1 → ((p2 ∨ (p4 ∨ (p3 ∨ (True ∧ ((p3 ∧ (True ∧ (p5 ∨ ((p2 ∨ False) → (p5 → p2))))) ∨ p3))))) ∨ p4))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350965167900134431479375948909 : (p4 → (((True → (((p3 ∨ (p5 ∧ p5)) ∧ p1) ∨ p3)) ∨ (p4 ∨ ((((False → (False ∧ p4)) → p4) → False) → (p4 ∨ p5)))) ∨ (p3 ∧ p3))) := by
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
theorem thm_5_vars_348029906133997909625279961926 : (p3 → ((p4 ∧ p3) ∨ ((p1 ∨ p1) ∨ ((p3 ∨ (p4 → p3)) → (p1 ∨ (((p2 → ((p3 → (True ∧ p5)) → (p2 → p5))) ∧ p1) → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159634479321368443659780732550 : ((((((((p1 ∨ True) → (p5 → p3)) ∨ ((p4 → False) → p5)) ∧ p1) → (p1 ∧ p1)) ∨ False) ∨ p3) → (p2 ∨ ((p3 → p1) ∨ (p1 → p1)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625264394240543033960864507956 : ((((True → (p5 ∨ (((p2 ∨ (p1 ∧ p1)) ∧ ((True → ((False → (p5 ∨ (False ∨ p3))) ∨ p2)) ∧ p1)) → ((p4 ∧ False) ∧ p1)))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_700617141328654026692063052113 : ((((p2 → (((p2 ∧ p4) → (((p2 ∨ True) ∧ p1) ∨ p5)) ∧ p4)) → (((p3 → p1) → (p4 → p5)) → (p2 → (True ∧ (p1 → p4))))) ∨ p3) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39108887745735451102092012715 : ((((p3 → p2) ∨ (p3 ∧ ((p5 ∧ (p5 ∨ (p1 → ((p1 ∨ (True ∧ p3)) ∧ (((p1 ∧ (p5 ∧ False)) ∧ False) ∧ p3))))) ∨ p2))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190371302101215684206826781539 : ((((p3 ∨ p3) ∨ ((True ∧ False) ∨ (p2 ∨ False))) ∨ True) ∨ (p5 ∨ (p3 → ((p2 → p3) → (((p5 → False) ∨ p4) ∧ (True ∧ (p3 ∧ False))))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147368804687923834199723549604 : (((((((p1 → p1) ∧ ((p3 ∧ True) → (True → p4))) → p3) ∨ False) ∨ (p2 ∨ (p1 → (p1 → True)))) ∨ p5) ∨ ((p3 ∧ (p3 ∧ False)) → p5)) := by
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
theorem thm_5_vars_318584867773889163694145291923 : (p4 ∨ (((((p4 → ((p3 → (p1 ∧ p4)) ∧ False)) → False) ∨ ((False → (p3 → True)) ∧ (False ∨ p5))) ∧ (True ∧ (p5 ∨ p2))) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116590424748602753936633847651 : (((p4 ∨ p4) ∧ (p1 ∨ ((((((((p1 ∨ (p1 → p5)) ∧ True) → (False ∧ p2)) ∨ (p1 ∧ p2)) ∨ False) ∨ p3) ∨ p2) → p1))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620314933682939181638229045404 : (((((p1 ∨ False) ∨ (((p1 → p5) → (((p3 ∧ ((p2 ∨ (True ∨ False)) ∨ (p3 ∨ p5))) → p5) → (False ∨ (False ∧ True)))) ∨ False)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_56381408841448366543184672724 : (((((True ∨ True) ∨ p5) → False) → ((True ∨ True) → (((p2 ∧ (p4 ∧ ((True ∧ ((p1 ∧ p4) → p4)) ∧ True))) ∨ (p3 ∧ p4)) ∧ p2))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : ((True ∨ True) ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : ((True ∨ True) ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h7
    -- False on the left can always be used.
    apply False.elim h8
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h9 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h10 : ((True ∨ True) ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h13 : ((True ∨ True) ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h14 := h1 h13
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172242588861748004531166527048 : ((((p3 → (p4 ∨ False)) ∧ (p1 ∧ (False → p4))) ∧ ((p4 ∧ (p1 → p5)) ∨ p4)) ∨ ((p3 ∧ p4) ∨ (True ∨ (p3 ∨ ((False → p2) → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57878679964009263909302246382 : (((p1 ∨ (p5 → p2)) → ((p3 → (False ∨ (p5 ∨ ((((False ∨ p1) → False) ∧ True) ∧ ((p2 → (p2 ∧ p4)) → (False ∨ True)))))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709671494788397026724974301712 : ((((p4 ∨ (False ∧ (False ∨ (p2 ∧ (p5 ∨ True))))) → (p3 ∨ (True → (((p5 ∨ (p1 ∧ (False ∨ (p3 ∨ p3)))) ∧ p5) ∨ (p1 ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777944086549980289534176261337 : (((p1 ∨ (((p2 ∧ False) ∨ p4) ∨ ((True → (p5 ∧ (True ∧ False))) ∨ ((((p1 → (p4 → (True ∨ p2))) ∨ p5) → (p3 ∨ True)) ∨ p4)))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181387598669575339883444020509 : ((p1 ∨ ((p3 ∧ False) ∨ (p4 ∨ (((p5 ∨ True) ∧ (p5 ∧ p2)) → p2)))) → (((p2 ∧ (True → p3)) → p1) ∨ (((False ∨ p5) ∧ True) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190260199318875400134764901117 : (((((p4 ∧ ((True ∧ True) ∧ p4)) ∧ p3) ∨ p3) ∨ p3) ∨ ((p2 ∧ (p3 ∨ ((False ∨ (p4 ∧ (True ∧ False))) → p1))) ∨ ((True ∨ p2) ∨ False))) := by
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
theorem thm_5_vars_859940678973499415313194681907 : ((((((p1 ∧ (((True → (((((p5 ∨ p1) ∨ False) ∧ p5) → p1) ∧ False)) ∨ (p5 ∨ (p1 ∧ p5))) → True)) → p4) ∨ (False → False)) → p1) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∧ (((True → (((((p5 ∨ p1) ∨ False) ∧ p5) → p1) ∧ False)) ∨ (p5 ∨ (p1 ∧ p5))) → True)) → p4) ∨ (False → False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255565341241367054407024018774 : ((p5 ∧ p3) → ((((False → (False → (False → False))) ∨ ((False ∨ p3) → p4)) ∨ ((p1 → False) → p4)) → (((True ∧ p2) → (p4 ∨ p1)) ∨ p3))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h1.left
      let h6 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h1.left
      let h9 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183869844356738609702856131943 : (((((False ∨ p4) ∧ (False → False)) → ((p1 ∨ p1) ∧ False)) ∧ p5) ∨ ((((True ∨ (p5 → ((p2 → p4) ∨ True))) → (p1 ∧ False)) ∧ p1) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ (p5 → ((p2 → p4) ∨ True))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597483700205715471286437322422 : ((((((True → p5) → (p4 ∧ p4)) ∨ ((((((p4 ∨ (False ∨ ((p2 ∧ p3) ∨ False))) ∧ p3) ∨ p5) → True) ∨ p3) ∧ (p2 ∨ p1))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151206245475832062757328066119 : (((((p4 ∧ (p3 → p3)) ∨ p4) ∧ (((p5 ∨ ((True ∧ p2) → p2)) ∨ ((p3 → True) → p5)) ∧ False)) → p1) → ((True ∧ (p1 ∨ True)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_48171549617817458250938679934 : ((((True → p5) ∧ ((((((False → ((True → p5) → (p1 ∧ True))) → (False ∨ True)) → (p3 ∨ True)) ∨ p3) ∧ p1) ∧ p4)) → (p1 → p5)) ∨ p4) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h13
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693034796262701657679307899324 : ((((True ∧ (True ∨ (((True ∨ p2) ∧ ((True ∧ p3) → (p5 ∨ p1))) → True))) ∧ ((((p3 ∧ p1) → (p2 ∧ p3)) → p1) ∧ (True ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699572891726136257490088166711 : ((((((False ∨ (p1 ∧ (p2 ∨ (True ∨ (p3 ∨ True))))) ∧ p3) → False) → (((True → ((False → p1) ∨ False)) → p1) ∨ ((p1 ∧ p1) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61445658203459000161351291876 : ((p1 ∧ ((False → (p4 → (p1 → (((p5 ∨ p4) ∨ ((p5 → ((False ∧ (False ∨ (p3 → p4))) ∧ (p5 ∧ p3))) → p3)) ∧ p3)))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315297940818830404045594645932 : (p3 ∨ (((p2 → p3) ∨ (p5 → True)) → (p5 ∨ ((((((p1 → p5) → p4) → p1) ∨ (False → ((p5 → False) ∨ p5))) ∨ (p4 ∧ p4)) ∨ p3)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45845726585412791731674186752 : (((p2 → (p2 ∧ ((((((p3 → (p5 ∧ False)) → p5) → True) → True) ∧ (p5 ∧ ((p2 ∨ (p1 → p2)) ∨ (p2 ∨ True)))) ∨ p3))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60126653437633641384745714922 : (((p4 ∨ True) → ((p1 ∧ (p5 ∧ (p3 ∧ ((((((((p2 → p2) ∨ (False → p1)) → p5) ∨ False) ∧ p4) ∧ p2) → p1) → p5)))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307880447823838217595316350879 : (p1 ∨ (p5 → ((p3 → (p2 ∧ True)) → ((p5 → ((p5 ∧ (((((True ∨ p4) → p2) ∧ ((p1 ∧ True) ∨ p2)) ∨ True) ∧ p3)) ∨ False)) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h18 =>
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h19 =>
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56667210682395374768964628714 : ((((False → False) ∧ True) ∧ (p2 → ((((p3 ∧ True) ∨ (((True ∧ p4) ∨ True) → p2)) ∧ p2) → (p1 ∧ (p5 ∨ (False ∧ (p2 ∨ p1))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349381612701849872552363852704 : (p3 → (p3 → (p4 ∨ (p3 → ((p2 → (p5 ∨ ((False → ((True ∨ (p5 → (p3 ∧ p1))) → (False ∧ True))) ∧ True))) → (p1 → (p1 ∨ p2))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594730396541413541271197611178 : ((((((p5 ∧ False) ∨ ((((p3 → (p1 ∧ p2)) → p5) ∧ (p4 → False)) → (p5 → p1))) → ((p2 ∧ (p3 → p5)) ∧ (False ∧ p1))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201030380114442081924340948781 : ((p4 ∨ ((p1 ∨ (False ∨ (p1 → p1))) → p3)) → ((p2 → (((False ∧ p4) → (p2 ∧ True)) → False)) ∨ ((p3 ∧ (True ∧ (p4 → p3))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (p1 ∨ (False ∨ (p1 → p1))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : (p1 ∨ (False ∨ (p1 → p1))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h8
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204339261485659054829784680478 : (((p5 ∧ (p5 ∧ (p5 ∨ False))) ∧ True) ∨ ((p5 ∨ (False → True)) ∨ (p4 ∧ (True → (False → ((p5 ∨ p3) ∨ ((False → False) ∨ (True ∨ p3)))))))) := by
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
theorem thm_5_vars_56747380960224371086045702970 : ((((False → p5) ∨ p5) ∧ (((False ∧ (p5 ∧ True)) → ((False ∧ p1) ∨ (p4 → (p3 → (p4 ∨ (p5 ∧ ((True → p2) → False))))))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_460351108502223981488148708740 : ((((True ∨ ((False ∧ p3) ∨ (p2 ∨ (((p5 → ((p1 ∨ p5) → p1)) ∨ True) ∨ (p1 → p1))))) → ((p4 ∧ p4) ∨ ((p5 ∨ True) ∨ p5))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h5
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
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
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h13 =>
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
theorem thm_5_vars_323988884071114729150093950779 : (p5 ∨ ((((p2 ∨ ((p4 → (p5 ∨ True)) ∧ (p4 → p3))) ∧ p1) ∨ (p4 ∧ p2)) ∨ ((p4 ∨ (p5 → True)) ∨ ((True ∨ (False → p2)) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_257688593908873864393166291865 : ((p3 ∨ p3) → (((((((((p4 ∨ p3) ∨ False) → p3) → True) ∨ False) → p3) ∨ (False ∨ p1)) → (p5 → p4)) ∨ ((p2 → p2) ∨ (p4 ∧ p5)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198255177839623341808283246275 : ((False ∧ ((p3 ∧ (p3 ∧ (True ∨ p4))) ∧ p1)) ∨ ((p3 ∨ (((p5 → p5) → (True → p5)) ∧ ((p2 ∨ p4) ∧ p5))) ∨ (False → (p4 ∧ p3)))) := by
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
theorem thm_5_vars_46566121387279187761052866538 : ((((p3 → p5) → (((p5 ∨ p4) → ((((True → (True ∨ p4)) → ((p5 → False) → p4)) → p2) ∧ (p4 → p2))) ∧ True)) ∧ (p4 → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183899116048471933063649284471 : ((((False ∨ False) ∨ ((True → (p1 → p2)) ∨ (True ∧ p2))) ∧ False) ∨ ((p2 → (((((p1 → p4) → (p3 ∧ True)) ∧ p1) → False) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678010112448569736378481083999 : ((((((True ∧ (p4 → p3)) → (((p4 ∧ ((p1 ∧ True) → p2)) → p1) ∧ True)) ∧ ((p1 ∨ p1) ∧ p5)) ∨ (True → ((False → p4) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147645086523141385858501368943 : ((((p5 ∨ ((((False ∨ p4) → (p5 → ((p2 → p4) ∨ (p4 ∨ p2)))) ∨ False) ∧ (p3 ∧ p2))) → False) → False) ∨ (True ∨ (p3 ∨ (p3 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305307527746587802635974105065 : (p1 ∨ ((((p3 ∧ True) → p5) → ((p1 ∧ (True ∧ ((((False → p2) ∨ p5) ∨ p3) → False))) ∨ p3)) ∨ (((True ∨ p5) ∨ p2) → (True ∧ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354610759261345712276571221228 : (p5 → (((((p3 ∨ (p1 → p4)) ∧ ((((p5 ∧ (((p5 ∨ True) → p5) → p2)) → p2) → (p5 → False)) → p4)) → (p5 ∧ p1)) ∨ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62920907319663117612811449057 : ((p4 ∧ (False ∧ ((p2 ∧ (False ∨ ((True ∨ ((p4 ∨ (p4 → False)) → p1)) → p1))) → (((True → p3) → p3) → ((p3 ∨ p4) ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693954415159884493694098012917 : ((((((p5 ∨ (p2 ∨ ((p1 ∧ False) ∨ (True ∧ p4)))) ∨ p1) ∨ (p3 ∧ p4)) ∨ (((((True ∧ False) ∨ False) ∧ p2) ∧ (p3 ∨ p3)) → False)) ∨ False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151871538890828452745321155495 : (((p5 ∨ (((p4 → (p5 ∨ (p1 ∨ False))) ∨ (True → p3)) ∨ (p3 → p4))) ∨ ((False ∨ (p5 → p3)) → True)) → (((False → True) → p2) → p2)) := by
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
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h5 : (False → True) := by
        -- Implications on the right can always be decomposed.
        intro h6
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h5
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h11 : (False → True) := by
            -- Implications on the right can always be decomposed.
            intro h12
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h13 := h2 h11
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h14 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h15 : (False → True) := by
            -- Implications on the right can always be decomposed.
            intro h16
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h17 := h2 h15
          -- One of the premise coincides with the conclusion.
          exact h17
      case inr h18 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h19 : (False → True) := by
          -- Implications on the right can always be decomposed.
          intro h20
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h21 := h2 h19
        -- One of the premise coincides with the conclusion.
        exact h21
  case inr h22 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h23 : (False → True) := by
      -- Implications on the right can always be decomposed.
      intro h24
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h25 := h2 h23
    -- One of the premise coincides with the conclusion.
    exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66089736630759882540981478718 : ((p5 ∨ ((((p1 ∧ ((p2 ∧ ((((p4 ∨ p3) → False) → ((p4 ∨ True) → ((False ∨ True) → True))) ∨ p1)) ∧ p5)) → p4) ∨ p1) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327201083809368310419904459090 : (True → ((p5 ∨ ((p4 → (((p1 → ((p1 ∨ p3) → p1)) → ((p5 ∨ p4) ∨ (p1 ∧ (False ∧ False)))) ∨ ((p5 → True) ∧ p3))) → p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597809782793063739333969496480 : ((((((p5 ∧ p5) ∧ True) ∧ ((p2 ∧ ((p1 ∨ ((p5 ∨ ((p4 ∨ p3) → ((True ∧ p5) ∨ p5))) → p1)) ∨ (p3 → p3))) ∧ p5)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753493977263932918673752536437 : (((False ∧ (((p4 → ((p3 ∧ p5) ∨ (False ∨ (((p2 ∧ ((False → p4) ∨ p4)) → p4) ∧ p1)))) ∨ p5) ∧ (p4 ∨ ((p5 → True) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54416238786551846407682236377 : ((((p5 → (False → ((p1 → p4) ∧ p5))) ∧ p5) ∨ (((p3 ∨ p4) → p5) → ((p5 → ((True → False) ∨ (p3 → (p4 ∨ False)))) ∨ True))) ∨ p3) := by
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
theorem thm_5_vars_226903977261583528348016805089 : (((True ∨ True) → p4) ∨ ((p2 → p3) → (((p4 ∧ (p4 ∧ p1)) ∨ ((p3 → (p1 → ((p4 ∨ (False ∨ p4)) ∨ True))) ∨ (False ∧ p5))) ∨ p5))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184185014773248990138907747915 : (((p5 → ((False ∨ (True ∧ ((p3 ∧ p3) ∨ p3))) ∧ p4)) ∨ p2) ∨ (p2 ∨ ((True ∨ ((p1 → p2) ∧ False)) ∨ (((p1 → p5) ∧ p4) ∧ p2)))) := by
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
theorem thm_5_vars_962606336049671929447006581343 : ((((True → p5) ∧ ((True → (p5 ∨ (((p4 → True) ∧ True) ∧ (p4 → (p2 ∨ True))))) ∧ (p1 ∧ (p2 → (p2 ∧ ((p5 ∧ p5) → True)))))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h8
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52628287101667495785972452313 : ((((p3 ∧ False) ∧ ((((p1 → (p1 ∨ p1)) ∧ (p5 ∧ p2)) → p3) → p2)) ∨ (((p5 → (p4 ∧ p1)) ∧ p4) ∧ ((p2 → p1) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165999804761722744328135345760 : (((p5 ∧ False) ∨ (((p3 ∧ p3) → p3) ∧ (p3 ∧ ((((False → p1) ∨ p2) ∨ p5) → False)))) ∨ (True ∧ ((True ∨ ((p5 → True) → p5)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_41392608738131171227254441824 : (((((True ∧ (True → p4)) ∨ (p3 → ((p5 ∧ (p1 ∧ p1)) ∨ (True ∧ p2)))) ∧ ((((False ∨ (True ∧ p1)) ∨ p4) → p2) → p2)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



