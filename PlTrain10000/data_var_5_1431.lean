variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172308169364602499704564312220 : ((((p3 ∨ False) ∨ (False ∨ (p2 ∧ (p5 → False)))) → (p3 → (p4 ∨ (p3 → p4)))) ∨ ((p2 → ((True ∨ p3) → (p2 ∨ False))) ∨ (False ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305778377827916731436439545994 : (p1 ∨ (((p2 → p5) → ((p3 → (p3 ∨ False)) → False)) ∨ ((p1 → (((((p3 ∨ True) ∨ False) → (p5 → p4)) → (False ∨ p4)) ∨ False)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45092930051742971598628798160 : ((((p5 ∧ p1) → (p2 ∧ ((p3 ∨ ((p5 ∧ (((p5 ∧ False) ∨ (True ∧ p1)) → ((True ∧ p4) ∨ False))) ∨ False)) ∨ (p2 ∧ p5)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214999710512578004082938641612 : (((True ∨ p1) → (p1 ∧ p3)) ∨ (((((((p4 ∧ ((p4 ∧ p1) ∧ p2)) ∨ True) ∨ p2) ∨ (p4 → p2)) ∧ (p1 ∨ (p1 → p3))) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114725651088368589349255548156 : ((((True ∨ ((p1 ∨ (False ∨ ((True → p4) ∧ p4))) ∨ False)) ∨ (p5 → (p1 ∧ p4))) → ((True ∧ (p4 → (False ∧ p4))) ∨ p5)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142202704170197460073872796285 : ((p1 ∧ ((p1 → (((p4 → True) ∨ p2) → ((p3 ∨ (False ∨ p3)) ∧ p5))) ∧ ((p1 → p2) ∨ (False → (True ∧ p3))))) → ((p5 → p3) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148984035463283551697288270962 : (((p5 ∧ (True ∨ False)) ∧ ((p5 ∧ ((((p3 ∧ False) ∧ p1) ∨ p4) ∨ (p3 → ((p2 ∨ p3) ∨ p3)))) ∧ p2)) ∨ (False → ((True → p1) ∧ p1))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341712625052461769984772981230 : (p2 → ((((((p4 ∨ (p1 → (p1 → p3))) → p4) ∨ (p3 ∧ p5)) ∧ True) ∨ ((False ∧ (p2 → (True → False))) ∨ (False ∨ p4))) ∨ (False → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166741899093891094184398939474 : ((p4 → (((p2 ∧ ((False ∨ ((p5 ∨ (p5 → p4)) ∨ True)) ∨ p1)) ∧ p3) → (p1 → False))) ∨ (((p2 → ((True ∧ p4) ∨ p2)) ∧ p1) → p1)) := by
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
theorem thm_5_vars_164697628270625789276554510031 : ((((((p1 → (((p2 ∧ p2) ∧ p5) ∧ (False → p4))) → p4) ∨ (p5 → False)) ∨ p5) ∨ True) ∨ (True → (((p5 ∧ p5) → (p3 ∨ p2)) ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52372924831366995905355335687 : ((((((True ∧ p1) → (p1 ∧ (p1 ∨ p5))) → p5) ∧ ((p4 ∨ p5) → p4)) ∧ (((p1 → (((p1 → p1) → True) ∧ p3)) ∧ True) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64098909402103908834994698620 : ((False ∨ ((p2 ∨ ((p4 ∧ (((p2 → p5) → p4) ∨ p5)) ∧ p3)) ∨ ((((p4 ∧ (p3 → p5)) ∧ (False ∨ p5)) ∨ False) → (p4 ∨ True)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760775378262918216146022831127 : (((p2 ∧ (p1 ∨ (((False ∨ p1) ∨ ((False ∧ False) ∨ p3)) ∧ (True ∧ ((p3 → ((False ∨ p4) ∨ (p5 ∧ (p1 → False)))) ∧ (True ∧ True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735968154567130238090367501233 : ((((True → p2) ∧ ((p1 ∨ p2) → ((p1 → p1) ∧ ((((p4 ∧ (p5 ∨ True)) ∨ p4) ∧ (True ∧ (((p1 ∧ p3) ∧ True) ∧ p5))) ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_220928083724962630334557048324 : (((p1 ∧ p1) ∨ True) ∧ ((p3 ∧ (p3 → (False ∨ (p3 → p2)))) → ((p4 ∨ (((p4 ∨ (True ∨ p4)) → p4) ∨ p2)) ∨ (p3 ∧ (p5 → p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136060123814342833681879718513 : ((((p4 ∧ (p1 ∧ (p3 ∧ (p5 ∨ p3)))) → p5) ∧ ((p1 ∧ (p1 ∧ (((False ∧ False) ∨ False) ∧ (p5 → p5)))) ∨ p4)) ∨ ((p5 → p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134391234846269659964855722579 : (((p5 ∨ (p2 ∨ ((((False ∨ (((False ∨ p1) ∧ p4) ∨ ((p2 ∧ (p1 ∨ p2)) ∨ p4))) ∧ p3) → p3) → p3))) ∨ True) ∨ (False ∨ (p5 ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123920963755356130130188374907 : ((((p5 ∨ ((p4 ∨ ((True ∧ p3) → False)) ∨ p3)) ∨ (p4 → p1)) ∧ (p2 → (False → (p3 → ((p1 ∧ (True → p2)) → True))))) → (p1 → p1)) := by
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
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h10 =>
          -- One of the premise coincides with the conclusion.
          exact h2
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123982532384847980305742931497 : ((((((p2 → p5) ∨ (p4 ∨ (p1 → p5))) ∨ p4) ∨ (True ∧ p1)) ∨ ((p4 → (((p3 → (False → False)) → p5) ∧ p5)) → p3)) → (p2 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
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
theorem thm_5_vars_148335039002831419442771412810 : (((((p1 → p5) ∧ ((p3 → (p4 ∨ ((p5 ∨ True) ∨ p3))) ∧ p2)) → p5) ∧ ((p1 ∧ True) ∧ (True ∨ p1))) ∨ (False → (p5 → (p5 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161121552771150601677744126569 : (((p5 ∨ False) ∧ (p2 ∨ (((((p4 ∧ p4) ∨ p4) ∨ (True → True)) ∧ p4) ∧ (True → (p3 → p5))))) → (p1 ∨ ((False ∧ (p2 ∨ p2)) ∨ p5))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319277582549937502874574744163 : (p4 ∨ ((((True ∨ False) ∧ ((False ∨ p4) ∨ True)) → ((((False → p3) ∧ p3) ∧ p2) ∨ p1)) ∨ ((True → ((False → p3) ∨ False)) ∨ (p1 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58511377507609239727206131915 : (((p4 ∨ p5) ∧ (True → ((False ∧ (((((p2 → False) ∧ (p5 ∨ (p5 ∨ (p4 → p4)))) ∨ p1) → p2) → ((p3 ∧ p1) ∨ True))) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48808202246854592414227342099 : (((p2 ∧ (True ∧ ((p5 ∧ (p2 ∧ ((p4 ∧ ((p2 → False) ∧ p5)) → ((True ∧ (p1 ∧ p5)) ∨ p2)))) ∧ p4))) ∧ ((p3 ∨ False) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174112513672325926553907184297 : (((p3 ∧ ((p4 → p3) ∧ (p2 ∨ (p3 ∧ (p5 ∨ (p3 ∨ True)))))) ∧ (p5 → True)) → ((((p1 → False) ∧ True) ∧ (p1 ∨ p5)) ∨ (False → p2))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
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
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- False on the left can always be used.
        apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180885347578428375700660447164 : ((((p5 ∧ p1) ∨ True) → (p4 → (((p4 ∨ p2) → True) ∧ (p1 ∧ False)))) → (((((p1 → (p1 → (False ∧ p2))) → p4) ∨ p3) ∧ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701181995123144469933329744413 : (((((((False ∧ (p4 ∨ p1)) → p5) → p1) ∧ (False ∨ p1)) ∧ (((p5 → ((p3 ∨ (True → p1)) → p2)) → ((p3 ∨ p3) ∧ p4)) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38567261126817548795329675309 : (((((p2 ∨ p1) ∧ (True ∧ (p4 → (p3 ∨ (False → p2))))) ∨ ((p1 ∧ (((p5 ∧ p3) ∧ True) ∨ (p1 → p5))) ∨ (p1 ∨ p3))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683979594289110707573383754412 : ((((((((p1 → (p3 ∨ (p5 ∧ p3))) → (p5 ∨ False)) → p5) ∨ ((p5 ∨ p5) ∨ p4)) → p2) ∨ (((False → p1) ∨ True) ∨ (p1 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51751533310303047073701187157 : ((((p2 ∨ p5) ∧ ((p5 ∧ p5) → (False → (p2 → (p3 ∧ (p4 → (False ∨ p3))))))) ∧ ((p3 → p4) → ((p2 ∨ p3) → (p4 ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52867292716741203286834467939 : (((p2 ∧ ((p4 → p5) ∧ ((((p3 ∨ False) ∧ p2) ∨ p2) → (p5 ∧ True)))) → ((p5 ∨ p5) ∧ ((p5 ∨ (p3 → p2)) → (p5 ∨ p3)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((p3 ∨ False) ∧ p2) ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h1.left
    let h17 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
    have h20 : (((p3 ∨ False) ∧ p2) ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h19, we can now drive its conclusion.
    let h21 := h19 h20
    -- We need to get the left conjuct of h21 based on <expert-advice>.
    let h22 := h21.left
    -- One of the premise coincides with the conclusion.
    exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184155620196913395523318550145 : (((p2 ∨ (p3 ∨ ((p1 → p3) ∨ ((p1 ∧ p1) ∨ True)))) ∨ False) ∨ ((p4 ∧ False) ∧ (True ∧ (((p4 ∧ (p3 ∨ p2)) ∨ (p2 → p4)) ∨ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_50311972447562762219023009115 : ((((p1 ∧ ((p5 ∧ ((p4 ∨ p1) ∧ ((False ∨ p3) ∨ True))) ∨ p2)) ∨ (True ∧ (p4 ∧ (p3 ∧ p4)))) ∨ (True → ((p2 → p3) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118183535111569334136783778263 : ((False ∨ (p5 ∧ ((p3 ∨ p2) ∨ ((p2 ∧ (((p3 ∨ (p4 → False)) → (True ∨ (((p5 ∨ p2) → True) ∧ p2))) → False)) ∧ p2)))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172617484955924231006067263466 : (((True ∧ p3) ∧ (p2 ∧ ((((False ∨ p1) ∨ (p1 ∧ True)) ∨ (p2 ∧ True)) ∧ p1))) ∨ ((True ∧ p1) → ((((True → p5) → p4) → True) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115857660326141155749708663554 : (((True → ((p5 ∨ p1) ∨ False)) ∧ (((p4 ∨ (True → p3)) ∧ p4) → (((p5 ∨ (p2 ∧ p4)) → False) ∨ ((False ∨ False) ∨ False)))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753432217202251418772921453312 : (((False ∧ ((True ∧ ((True ∨ ((False ∨ (p2 ∨ p1)) ∧ ((p3 ∧ p3) ∨ True))) ∧ (((p3 ∨ p4) ∧ p5) ∨ p2))) ∨ (p3 ∨ (p5 ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141294818965479514802778967067 : (((True ∧ (False → (p5 → True))) ∧ (((False ∧ ((False → p2) ∧ (True → p2))) → True) → (((p1 ∧ p2) ∧ False) ∧ p2))) → (p2 → (False ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h7 : ((False ∧ ((False → p2) ∧ (True → p2))) → True) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h7
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h16 : ((False ∧ ((False → p2) ∧ (True → p2))) → True) := by
    -- Implications on the right can always be decomposed.
    intro h17
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h18 := h13 h16
  -- We need to get the left conjuct of h18 based on <expert-advice>.
  let h19 := h18.left
  -- We need to get the right conjuct of h19 based on <expert-advice>.
  let h20 := h19.right
  -- False on the left can always be used.
  apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190664539915595016293997421474 : (((True → (p1 ∧ (p4 → ((p5 ∨ p5) ∧ p5)))) → False) ∨ ((False ∨ (p2 ∧ p5)) → (((p2 ∨ p4) → ((p3 ∨ True) → p1)) ∨ (p1 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158298183631773962674320947188 : ((((p2 ∧ p4) → p4) → (((p1 ∧ p3) ∨ ((False ∨ p3) → (p1 ∨ p1))) ∧ ((False ∧ True) ∧ p1))) ∨ ((False → False) ∨ ((p2 → p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165597788882727440070341229479 : ((((((True ∧ True) ∧ True) ∨ (p1 ∧ p3)) → p2) → (p5 → (p3 ∨ (p4 ∨ (p3 ∧ p3))))) ∨ (p3 → (True ∨ (p1 → ((p1 → p1) ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161445175222013375737078394073 : ((p2 ∧ (p2 ∨ (p5 ∧ ((p1 ∧ p2) ∧ (((((True → p5) ∨ False) ∨ True) ∨ (p5 ∨ True)) ∧ p2))))) → ((p4 ∨ ((True ∧ p4) → True)) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h9.left
    let h13 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h17 =>
          -- False on the left can always be used.
          apply False.elim h17
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h19 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688911578132110055431921127727 : ((((((p2 → p5) ∨ ((p4 → (p4 → (((p3 ∨ p1) → p5) → p5))) ∧ True)) ∧ p4) ∨ (((((p3 ∧ p5) ∧ True) ∨ p4) ∨ p4) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_114965543001719741642294629527 : (((False → (p3 ∨ ((((p5 ∨ True) → (p4 ∧ (False → p1))) ∧ p5) ∨ p5))) → (False ∧ (((True ∧ p5) ∧ p3) ∨ (False → p1)))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234387687617988666848354082398 : ((p1 → (False → p3)) → (p4 ∨ (p3 → (True ∧ ((p5 ∨ ((((p4 ∧ p1) ∨ p4) ∧ ((False ∨ p4) ∧ True)) ∨ (False ∨ p3))) ∨ (p5 ∨ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69268925910637794037507419427 : ((p5 → ((p2 ∧ p2) ∨ (((((p3 ∧ (p2 ∧ p1)) ∨ ((p4 ∧ p2) ∨ (p3 → (p1 → (p5 → p1))))) ∧ False) ∨ (p3 ∨ p4)) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173825251033057818409997055153 : (((p3 ∨ (((p4 ∨ (((False ∧ False) ∧ (p3 ∧ True)) ∨ p1)) ∧ False) → p4)) ∨ p4) → ((p5 ∨ p2) ∨ ((p5 ∨ p4) → ((True ∨ p4) ∨ p4)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192032933481957759479676526299 : ((p2 → (((p4 → p2) ∧ p5) ∧ ((p3 ∨ p2) ∧ False))) ∨ (((p1 → ((p2 → p4) → (((True ∨ p2) ∧ p4) → p3))) → p5) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226434713252177362751433342217 : (((p1 → False) ∨ p1) ∨ ((((p3 → (True → p2)) ∨ p2) → p4) ∨ (False ∨ (True → (p1 ∨ (False → ((False → True) ∧ (False ∧ (p5 ∧ True))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140738392745473120164038093543 : ((((True ∧ (p1 ∧ (p3 ∧ ((p1 ∧ (p2 ∧ (True ∧ p2))) ∧ p3)))) → p2) → (((p2 → p1) ∧ False) ∧ (p3 ∧ True))) → (True → (p3 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((True ∧ (p1 ∧ (p3 ∧ ((p1 ∧ (p2 ∧ (True ∧ p2))) ∧ p3)))) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- One of the premise coincides with the conclusion.
    exact h18
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h19 := h1 h3
  -- We need to get the left conjuct of h19 based on <expert-advice>.
  let h20 := h19.left
  -- We need to get the right conjuct of h20 based on <expert-advice>.
  let h21 := h20.right
  -- False on the left can always be used.
  apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63415158939665338452568107046 : ((p5 ∧ (p5 ∨ (p3 ∧ ((p1 ∧ p3) → ((((((False ∧ (p1 ∨ p3)) → (p4 ∧ p1)) → p3) → p3) → p4) ∨ ((p2 ∧ False) ∧ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612632636721188720718409794144 : (((((((p5 → p2) ∧ (p1 ∨ (True → ((True → (p3 ∨ (p1 ∧ True))) → ((p4 → p4) ∧ p2))))) → (p4 ∨ p5)) ∨ (p5 ∨ True)) ∨ p3) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608624557954153018223391522797 : ((((((p5 ∧ ((((p4 → (False ∧ ((p3 ∧ (False → p3)) → ((True → p1) ∨ False)))) → False) ∨ p3) ∨ p1)) ∧ (p5 ∨ p1)) ∨ True) ∨ p3) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_47978840938958355996179424262 : (((((((p3 ∧ (p5 ∨ (((p3 → (p3 → True)) ∧ p4) ∨ p1))) ∨ p5) → p3) ∧ p5) → (p1 ∧ (p4 ∨ (p4 ∧ False)))) → (p2 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721306215303091250891164030792 : (((((p2 → p5) → (False → True)) → (((p1 → p2) → (p3 → p2)) → ((((p1 ∧ ((p1 → p1) ∨ p5)) ∧ p5) ∧ False) ∨ (False → p4)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52345262814051746354700309929 : (((((False ∧ p4) → ((p3 → p3) → (((p1 ∧ p3) ∧ p5) → p5))) → p2) ∧ (((p5 ∧ (((False ∧ p2) → p3) → False)) ∨ p2) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135469820244340880434914469874 : ((((p2 → (((p1 ∧ True) → ((p1 ∨ p5) ∨ p3)) ∨ (p5 ∧ p4))) ∧ ((p3 → True) → p4)) → ((p3 ∨ p2) ∨ p3)) ∨ (False ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262249697917737914062844874002 : (True ∧ (((((True → (((True ∧ False) → True) → (((p4 → p3) ∧ (p5 ∨ p5)) ∧ p3))) ∨ p5) ∧ (False ∧ p1)) ∧ ((p5 ∧ p3) ∧ True)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612840544175319713564265460100 : (((((False ∧ (((p1 ∨ p1) → p4) ∨ (((((p3 → True) ∨ p2) ∧ (True → (p4 ∨ p3))) ∨ True) → (p5 ∧ p5)))) ∨ (p2 → True)) ∨ p3) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342920729792736936119166972241 : (p2 → ((((p5 ∧ True) → p2) ∧ p2) ∧ ((p2 → (p5 → (p4 ∨ (True → (True → (p2 → p1)))))) → ((p1 → (p4 ∧ p4)) ∨ (False → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190392760632497944572761710548 : (((p1 ∧ ((p3 ∨ ((p3 ∨ p3) → False)) → False)) ∨ True) ∨ (True → (((False ∨ (p3 ∧ ((p1 ∧ p2) ∧ p3))) ∧ p1) ∧ ((True ∧ p5) ∨ p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313113759141242640833433841079 : (p3 ∨ (((p4 → (p2 ∧ ((p3 ∧ (((False → (p1 ∧ p1)) ∨ p4) → (p5 → p5))) ∨ (p5 ∨ (p4 ∨ p2))))) ∨ ((p5 → p3) ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174155872726238677730872940000 : ((((p2 → (p4 → (p5 → (True → p4)))) ∨ ((True ∨ False) → False)) ∨ (False → p1)) → (p2 → (p4 ∨ (((p1 ∧ False) ∨ (False → p2)) ∨ False)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h7 : (True ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h8 := h6 h7
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54671628197317300522508270969 : (((((p3 → (p1 → (p2 → p3))) ∧ p4) → p3) → ((True → p2) → (((True → p4) ∨ p3) → ((p2 ∧ (p4 ∧ (p1 → p5))) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751041500808606582478576908886 : (((True ∧ ((p2 ∨ ((p4 ∧ p3) ∧ False)) ∧ ((((True → p3) ∨ ((p4 ∨ False) → ((True ∨ p5) → p2))) → p1) ∨ (True → (p1 ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147687464581131852135208817005 : ((((((p4 ∧ p4) → (p3 → (((False ∧ True) → (False → p5)) → p5))) → p4) → ((p4 ∧ p2) → p3)) → p2) ∨ ((False ∨ p2) → (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183864773127627938157013121246 : (((((False ∧ p3) ∨ (True ∨ p4)) ∨ (p1 ∧ (p3 ∨ p4))) ∧ p4) ∨ (((True → (p3 → p5)) → (False → p3)) ∧ (p4 → (False ∨ (p3 ∨ p4))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184715220881693378531958877789 : ((((p3 ∨ p3) → ((p2 → p2) → p1)) → ((p3 → True) → p2)) ∨ (((p4 ∨ False) ∨ ((p1 → (p2 → p5)) → p1)) → (False → (p5 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33873885614362450750079412209 : ((p5 ∨ ((((True ∨ p1) ∨ (False → (p3 ∧ p2))) → True) → (((True ∧ ((p3 ∧ p2) → p2)) → False) → ((p2 ∧ (p4 ∨ p2)) ∨ False)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True ∧ ((p3 ∧ p2) → p2)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h3
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60883172527505288550874230823 : ((True ∧ (p2 → (((p4 ∨ (((((True → ((p2 ∧ p3) ∧ p5)) ∨ p2) ∧ (p5 ∨ p3)) ∧ (False ∨ p1)) ∨ (p5 → False))) ∧ False) ∨ True))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715060880350375070639612575846 : ((((p2 ∨ (True → (False ∨ (p3 → p3)))) → ((p2 → (p5 → (((((p1 ∨ False) ∨ p5) → p3) ∨ False) ∨ True))) ∨ ((p1 ∧ True) ∨ True))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179065300630309269842054248349 : ((True ∧ ((((p3 ∨ (True ∧ p5)) ∧ True) ∧ (p1 ∧ (p4 → p4))) → p4)) ∨ ((((((p4 ∧ True) ∨ p5) ∧ p2) ∧ p4) ∨ (True ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67869119255141475203254915605 : ((p2 → ((p4 ∧ (((True → (p3 ∨ False)) → p2) ∧ ((((False ∧ p1) ∧ p4) ∧ (p5 ∨ p4)) ∨ (p4 ∧ p4)))) ∨ (True ∧ (True ∧ True)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679150841006632546332654564691 : ((((p3 ∨ (True → (p5 ∨ (p5 → (((True ∧ ((p4 ∨ (p3 → p1)) ∨ False)) → (p1 ∧ p2)) ∧ p5))))) ∨ (((False ∧ p2) → False) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66104021892019806078220206426 : ((p5 ∨ (((((((p3 ∨ (p1 ∨ (True ∧ p4))) → p2) ∧ p2) → p2) ∧ p3) → (p5 ∨ ((p2 ∨ ((p3 ∨ False) ∧ p4)) ∨ p4))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209441351687543186833814232970 : ((p2 → (p3 ∧ (p4 ∨ (p4 → True)))) → (((p3 → (p4 ∧ p4)) ∧ False) ∨ (False → (p2 → (p3 ∧ ((True ∨ p3) → ((False ∧ p4) ∧ p5))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312960218913315548099727341860 : (p3 ∨ (((((p1 → p3) → (p1 ∨ ((False ∧ ((((p5 → (p4 ∧ p5)) → p3) ∧ (p4 ∧ False)) ∨ (False ∧ p5))) → p4))) → p4) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650003428485906263275351530196 : (((((True ∧ (((p3 ∧ False) ∧ ((p5 ∧ ((p5 ∧ p4) ∨ p5)) ∨ False)) ∧ (p1 ∧ (p5 ∨ False)))) ∨ ((p5 → p2) → True)) ∧ (p3 ∨ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661937355548852461141125185536 : (((((((p4 ∧ (p2 ∧ p1)) → (((p3 ∧ p4) ∨ p4) ∧ (p2 → True))) ∨ p1) ∨ ((p1 ∨ True) ∨ (False ∨ (p5 → False)))) → (p2 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186725661324832105506879730655 : (((False ∨ (((False ∨ p1) ∨ True) → False)) ∨ (True ∧ (p3 ∧ p4))) → ((p2 ∨ True) → (((p2 → p1) ∧ (((p5 → p5) → True) → p3)) → p3))) := by
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
  cases h2
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h10 : ((False ∨ p1) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h11 := h9 h10
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h21 : ((False ∨ p1) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h22 := h20 h21
        -- False on the left can always be used.
        apply False.elim h22
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- One of the premise coincides with the conclusion.
      exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40636449336213143799507436406 : (((((((p4 ∨ (p5 ∨ (False → p1))) ∧ (p5 → (p1 → p5))) ∧ ((False ∧ p4) ∧ (p2 ∨ (p1 ∨ (p1 ∧ p2))))) → p1) → False) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65754022763387203961100540666 : ((p4 ∨ (((p4 → p5) ∧ ((p5 → p1) → (((p3 ∧ p1) ∨ (p5 → ((p5 → False) ∨ False))) ∧ p4))) ∧ (p1 ∨ (True ∨ (p3 ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769503464282430511850107073490 : (((p5 ∧ (p3 ∧ (((p3 ∨ (((p1 ∨ p4) → p2) ∧ ((p2 ∧ True) → p2))) ∧ p5) → (False ∧ ((False ∨ p3) ∧ ((False ∧ False) → True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756021311124929280579799866285 : (((p1 ∧ (((p4 ∨ False) → ((p2 ∨ (((True ∨ (False ∧ (p2 ∧ False))) ∨ ((p5 ∨ True) ∨ (p5 ∨ (True ∧ p4)))) ∧ p2)) → p1)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205503799286662827863722371282 : (((p3 ∧ p3) ∧ ((p2 ∧ False) ∨ False)) ∨ (p1 → ((((p3 ∧ (True → ((True ∨ p4) → (p2 ∧ False)))) ∧ (False ∧ p5)) ∨ p1) ∨ (p2 → True)))) := by
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
theorem thm_5_vars_196773016004973371248349192969 : ((((p3 ∨ (p2 → True)) → (p4 ∨ False)) ∧ False) ∨ ((False → (((False → p5) → False) ∨ ((p3 → False) ∨ False))) ∧ (p3 ∨ (False → (p2 ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42855000975610984992894525146 : (((p2 → (((p5 ∧ (p2 ∨ (p1 ∧ ((p2 ∧ True) → p2)))) ∨ (((False ∧ False) ∧ p2) ∨ (True ∧ p5))) ∨ ((p5 ∨ p4) → p4))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118727100674748206360912932462 : ((p5 ∨ ((True ∧ (p3 → (p5 ∨ (((p3 ∨ True) ∨ (p3 ∨ (p4 → (p3 → p1)))) ∨ p1)))) ∧ (((p4 ∧ p4) ∨ False) ∧ p1))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308411050951912183216975910793 : (p2 ∨ (((((False → ((True ∨ (((((p1 ∧ False) ∨ (p5 → p2)) → p3) ∨ p3) ∨ p3)) ∧ True)) ∨ (p3 ∧ (p2 ∨ p4))) ∨ False) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715254019789135646551669156254 : ((((p2 → ((p3 ∧ (p3 ∨ p1)) ∧ p2)) → (p4 → (p4 ∧ (((p3 → p5) ∨ (((True ∧ p1) → p5) → (p1 ∨ (p4 ∧ p3)))) ∨ p4)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166306873327226563930013214804 : ((p4 ∧ (p2 → ((p1 ∨ p2) ∧ (((p2 ∨ True) ∨ True) → ((p1 ∧ (True → p1)) ∨ False))))) ∨ (((False → (p5 ∨ True)) → (True → p2)) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → (p5 ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178096868686194191544462017361 : ((((p5 → (((False → (p3 ∧ (True ∨ p3))) ∧ False) ∨ p3)) → p4) → p5) ∨ (p1 ∨ (p2 ∨ ((p1 ∧ False) → (((p3 ∨ p2) ∧ False) → p1))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655555984552419191458868469532 : (((((((p1 → p2) → (p2 ∧ ((((p4 → False) ∨ p3) ∨ p5) ∨ p2))) → (p1 ∨ (p2 ∧ (p5 → p2)))) → (p2 ∧ p4)) ∨ (False → p5)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_148634531834312712147600697187 : (((p1 → ((False → (p1 → (p5 ∧ (True ∧ p2)))) → p3)) → ((p5 → ((p4 ∨ p1) ∧ (p4 ∨ p5))) ∧ p4)) ∨ (True → ((p5 → p5) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148670828442841471950814459536 : ((((p3 → (((False ∨ p3) ∧ p4) → True)) ∧ p1) ∨ (((p2 ∧ p3) → (((p2 → p3) → p1) ∧ p3)) → p1)) ∨ (p3 → (True ∨ (False ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63920153206825445245564035852 : ((False ∨ ((p5 → (p4 ∨ (((p2 ∧ p1) ∧ ((True → p4) ∧ p5)) → (p1 → (p2 ∧ (p2 ∧ ((p4 → (False ∧ p3)) ∧ p5))))))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45895070756224283312620380283 : (((p4 → (((p2 ∧ ((((((p5 ∧ False) ∧ p2) → p1) ∧ (((p3 ∧ p5) → p2) → p4)) ∧ p4) → (p3 → True))) ∨ p2) ∧ p1)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214600362393808722581967808441 : (((p5 ∨ True) ∧ (p2 ∨ False)) ∨ (((((p3 → p5) ∨ p5) ∨ False) ∨ (((p1 ∧ p2) ∧ p5) → (p2 ∧ (((p2 ∨ p4) ∨ p5) → p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158054389888000913584728638266 : (((False ∧ (p2 ∧ (p5 ∨ (p5 ∧ p4)))) ∨ (((False ∧ ((p1 ∨ p5) ∨ True)) ∨ p5) ∨ (True ∨ p1))) ∨ (p2 ∨ (((p2 ∨ p2) → p5) ∧ p1))) := by
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
theorem thm_5_vars_49245312417700618190097159781 : ((((p1 → p2) → (p1 ∨ (p2 ∧ ((((p4 → p2) ∨ p4) → (((p3 ∧ p1) → p3) ∨ p3)) ∧ (p3 ∨ p2))))) ∨ ((p2 → p2) ∨ p3)) ∨ p5) := by
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



