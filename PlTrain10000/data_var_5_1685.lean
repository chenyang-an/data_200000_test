variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141994819953656260873750790951 : (((p5 ∨ p3) → ((p5 → True) → ((((True → p4) ∨ (p4 ∨ ((p4 → (p3 ∧ p4)) ∧ False))) ∧ p3) ∧ (p5 → p2)))) → ((p2 ∨ True) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327789333038664695991398977325 : (True → ((((((p3 → (p4 → p2)) ∨ False) → ((p4 ∨ (False ∧ (((False → (p2 ∧ True)) → p1) ∧ p5))) ∨ p5)) ∨ p5) ∧ p4) ∨ (True ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712672327971386827393637305367 : (((((p2 ∨ p2) ∧ ((p2 ∧ p5) ∨ p4)) ∨ (p3 → ((p4 ∧ p2) ∨ (True ∨ ((((p4 → p5) ∧ ((False → p3) → p5)) ∨ p4) ∨ p1))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588811684295724153766218909752 : (((((False ∨ ((((p4 ∨ (False ∧ (p4 ∧ (p1 ∨ p3)))) ∨ False) ∧ ((p1 → ((False → p1) ∨ (p2 → p5))) ∧ True)) ∨ True)) ∨ False) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684680782545683430581930610314 : ((((((p5 ∧ p3) → p3) → ((((False → p1) ∨ False) ∧ (p1 ∨ ((False → True) → True))) → p2)) ∨ ((p5 ∧ (True → (p5 ∨ p2))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613976995779201412179299874900 : ((((((p1 ∧ (p2 ∨ ((p2 ∨ False) → (p4 → p3)))) ∧ (((p4 ∨ p4) ∨ ((p5 ∧ p2) ∨ p1)) ∨ p2)) ∨ (p3 ∨ (p2 ∧ False))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114393912171365491986489589695 : ((((True → ((((p4 → p1) → (p1 ∨ p2)) → p4) ∧ (p4 ∧ p5))) ∨ (p3 → (p4 ∧ p4))) ∨ ((True ∧ True) ∧ (p2 ∧ p4))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148040825924400548106798769845 : ((((p5 ∨ True) → ((p1 ∨ ((p1 ∧ (p4 → (p5 → (p5 ∧ (p2 → p1))))) → p3)) → p5)) ∨ (False → p2)) ∨ (((True ∨ p1) ∧ p3) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192980472603120033212052046838 : (((p5 → ((p2 ∨ p4) → (False ∧ True))) ∨ (False ∨ p1)) → (((False → True) ∨ (p1 → p2)) → (False ∨ ((p5 ∨ ((True ∨ p1) ∨ True)) ∨ False)))) := by
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
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
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
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
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
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
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
theorem thm_5_vars_168023154587544214750403113276 : (((p3 ∨ ((True ∧ False) ∨ (p2 ∨ p4))) ∨ ((((True ∧ p1) ∧ (False → p3)) ∨ p2) ∧ p5)) → ((((p5 ∨ (False → p4)) ∧ p1) ∨ True) ∨ p4)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
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
        cases h8
        case inl h9 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h19 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62126098991378917908162420594 : ((p2 ∧ (p3 ∨ (((p3 ∧ ((True ∧ ((p3 ∨ ((p5 ∧ p5) ∧ ((p1 ∨ p4) ∨ p5))) ∨ (p2 ∨ True))) → p3)) → p3) → (p4 → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158514159670928035075108335932 : (((p2 ∨ True) → ((p2 ∧ (p4 → ((p2 → ((True → p5) → p2)) ∧ ((p3 ∨ p5) ∧ False)))) ∨ True)) ∨ ((((p2 ∧ False) ∨ False) ∧ p2) ∨ p1)) := by
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
theorem thm_5_vars_58867724035846790866548309339 : (((False ∧ True) ∨ ((p5 → (((((p5 → (p5 → p1)) → p3) ∧ p3) ∧ (p2 ∧ (False → p1))) ∧ ((p1 → True) → (p3 → p3)))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202257450013946012214559940852 : (((False ∨ ((p2 → True) → False)) → p1) ∧ ((p2 ∨ (p5 ∧ (p2 ∨ (((p3 ∨ p2) ∧ p5) ∧ p1)))) ∨ ((p4 → p4) → ((True ∨ False) ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (p2 → True) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- False on the left can always be used.
    apply False.elim h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137338228363393413655044948034 : ((p2 ∧ (p4 ∨ (p3 → ((p4 ∨ ((((p2 ∧ False) → (p1 ∨ (p1 ∨ False))) ∧ p4) ∨ ((p4 → p1) ∨ p1))) ∨ p4)))) ∨ ((p2 ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151788759194853305699895634131 : (((p3 ∨ (((p3 → (p4 → (p2 ∧ (((True → p1) ∧ p4) → p2)))) ∧ p2) ∧ p3)) → ((p3 ∨ p4) → p4)) → ((p1 → (p2 ∨ True)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318669370395217443685706574066 : (p4 ∨ (((p3 ∨ (p3 → ((((True → (p3 → (True ∨ ((p4 ∨ p3) → (p1 ∨ p3))))) ∨ p1) → (p1 → p1)) ∧ p2))) ∧ p5) → (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_878037312456558093148120326102 : (((((p2 ∧ p1) ∧ (((p3 → ((p4 ∨ p4) ∨ ((p3 ∨ (p1 → p3)) ∧ p3))) → (p3 ∧ ((True → p1) ∧ p3))) ∨ p3)) ∧ (True ∨ p5)) → p3) ∧ True) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h10 : (p3 → ((p4 ∨ p4) ∨ ((p3 ∨ (p1 → p3)) ∧ p3))) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h12 := h8 h10
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h15 : (p3 → ((p4 ∨ p4) ∨ ((p3 ∨ (p1 → p3)) ∧ p3))) := by
        -- Implications on the right can always be decomposed.
        intro h16
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h17 := h8 h15
      -- We need to get the left conjuct of h17 based on <expert-advice>.
      let h18 := h17.left
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h20 =>
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h21 =>
      -- One of the premise coincides with the conclusion.
      exact h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803770789996450554544890920618 : (((p3 → ((False ∧ (p4 ∧ ((p1 ∧ (p1 ∧ p1)) ∨ (p1 ∨ ((p4 ∧ p2) → (p2 → ((p4 ∨ (p2 ∨ p3)) ∧ p1))))))) ∧ (p3 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697835892319353173425163311068 : (((((((p4 ∧ (p5 ∧ (p5 → (p3 ∨ p3)))) ∨ True) ∧ False) ∧ False) ∨ (p5 → (True ∧ (((p3 ∨ (p1 ∨ p3)) ∨ (p5 → p1)) ∨ p5)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37760567206079425647006953459 : (((((p3 ∨ (False ∧ (False ∨ p2))) → ((False → (p2 ∧ ((p5 ∧ True) ∧ ((p4 ∧ p3) → True)))) → (p5 → (True ∨ p3)))) → p5) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49654677288354796713396605373 : (((((True ∨ p3) → p5) ∧ ((((p2 → p1) ∨ ((((p1 → False) → False) → False) → (p2 ∨ p3))) ∨ p4) ∨ True)) → ((p5 ∨ p3) ∨ p4)) ∨ p3) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h7 : (True ∨ p3) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h8 := h2 h7
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h10 : (True ∨ p3) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h11 := h2 h10
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : (True ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h14
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60301422995927475496998457587 : (((p1 → p2) → (((p4 ∨ (p3 → p5)) ∨ (((p4 ∧ True) → (p5 ∧ (((True ∧ False) ∧ p4) → (False ∧ p3)))) ∨ (p4 ∨ p5))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655874715118101079701671862039 : ((((((True ∨ True) → ((True ∧ ((p2 ∨ ((p2 → p2) ∧ p3)) → p5)) → ((p2 ∨ p1) ∨ p4))) → (p5 → (p3 ∧ True))) ∨ (True ∧ True)) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53483644613851233290489501388 : (((p3 ∧ ((p2 ∨ ((p5 ∧ (False ∨ (False ∨ p4))) ∨ p1)) → True)) → (((p2 → p2) ∧ (p1 → (False ∨ (p5 ∧ False)))) ∧ (p3 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47855768814380366727937212226 : ((((p4 → ((((p4 ∧ (False ∨ p1)) → ((p1 ∨ (p1 ∧ ((p5 → (True → p2)) → p5))) ∧ p3)) ∨ p5) ∧ p3)) → p4) → (p4 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241820372827191389087574338268 : ((p1 → p1) ∧ ((((((((p1 → p2) → (p3 ∨ (p2 → False))) → False) ∧ ((p2 → False) → p2)) → (p2 ∨ p5)) ∧ True) ∨ (False → False)) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44052754529795281692906847251 : ((((p3 → (((p5 ∨ (p4 ∨ p2)) ∨ ((p5 ∧ (False → ((p2 ∧ p3) ∨ p5))) ∧ True)) ∧ (p5 ∨ (False ∨ p2)))) → (p2 ∨ p1)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776617681611651987988246524312 : (((p1 ∨ ((p2 ∨ ((p2 ∨ (p5 → (((True ∧ p2) → (p3 → p5)) ∧ p3))) → ((p3 → False) ∨ (False → ((p5 ∧ False) ∧ False))))) ∨ p1)) ∨ False) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h5
    -- False on the left can always be used.
    apply False.elim h5
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349109006872021705129764096794 : (p3 → (True → ((((p5 ∧ (False ∨ (p1 ∧ p2))) ∧ True) ∨ ((p1 → True) → (p5 ∨ (False ∨ (False → p5))))) ∧ ((False ∧ p2) → (p2 ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658444040405487749282923872476 : ((((p1 ∨ ((p4 → ((p1 ∨ True) ∨ (((True ∨ (p3 → p5)) ∨ True) → ((True ∧ p3) → (p4 → (p4 ∧ p2)))))) → False)) ∨ (p3 ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_49628800968498857506368802317 : (((((p3 → (True ∨ p2)) ∧ (p5 → True)) ∨ ((p5 ∨ ((False ∧ True) ∧ p4)) → ((True ∨ True) → (p3 ∨ p5)))) → ((p4 ∧ p3) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50154005330661571448749083458 : (((p2 → ((p1 ∨ p1) → (p4 → (((False → ((False → p4) ∧ p2)) → (p3 ∧ (p2 ∧ True))) ∧ p4)))) ∧ (p5 ∧ ((True ∨ p5) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42741699279691999897500602918 : (((True → ((p5 ∨ (p1 ∨ ((p1 → (False ∧ (p5 ∧ p3))) ∨ False))) ∨ (False → ((False → ((p5 ∧ False) ∨ (p4 ∨ p5))) ∨ p1)))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345616901684104743311239633782 : (p3 → (((p2 → p4) → ((((p2 ∨ (True → (p2 ∧ p3))) → ((p5 ∨ ((True → True) → p1)) ∧ p3)) → ((p3 → False) ∧ False)) → p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164836601709541763754377152525 : (((p1 ∧ ((p2 ∨ p3) ∨ ((True → p4) ∧ (p4 → (p5 ∧ ((p4 ∧ True) ∧ False)))))) ∨ True) ∨ ((((True → p1) ∧ (p4 ∧ True)) → True) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238194383103537830820881888386 : ((True ∨ p4) ∧ (((((p2 → False) ∧ p3) ∨ (p1 ∨ ((p5 → False) → (True → p3)))) ∧ (True ∧ (p1 ∧ p1))) ∨ (p4 → (p3 → (p4 ∧ p3))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151405532914269591445174772650 : (((((p1 ∨ True) ∨ (False → False)) ∨ (False → ((p3 → ((False → False) → p4)) ∨ (p1 ∨ p5)))) ∧ (p3 → True)) → ((p4 → p3) ∨ (True ∨ p4))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114939780482182693179717222192 : (((((True → p1) ∨ (False ∧ p4)) → ((p3 → ((p3 ∧ p3) ∧ p4)) → False)) → (p5 ∨ ((p4 ∧ (p4 ∨ True)) ∨ (p5 ∧ p4)))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1815459721648453897470637270 : ((p4 ∨ (((((False → p4) ∧ p5) ∨ ((p1 ∨ (p1 ∨ (((p2 → p3) ∨ p2) → False))) ∧ False)) ∧ False) ∨ True)) ∨ ((p5 → p3) ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121040021532804793814501194981 : ((((p1 → p1) → ((True ∧ (False ∨ (((p4 ∨ p5) ∨ (p4 ∧ p2)) ∨ ((p5 ∧ True) ∨ p4)))) ∧ (p3 ∧ (True → False)))) ∨ False) → (p1 ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h3
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h11 =>
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h14 := h11 h12
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- We need to get the left conjuct of h15 based on <expert-advice>.
    let h16 := h15.left
    -- One of the premise coincides with the conclusion.
    exact h16
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46365683006080190605864980227 : (((((p1 → ((p1 ∧ ((p2 ∨ p5) → False)) ∧ False)) ∧ (p4 ∨ True)) ∨ (True ∧ (p3 → (p1 → (p4 ∧ (p3 ∨ p3)))))) ∧ (p5 → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135685942872758994193834043670 : ((((p3 ∨ ((False → (False ∨ ((True ∧ p4) → p4))) → (p2 ∨ p4))) ∨ p3) ∧ (((p4 → (p5 ∧ p3)) ∧ p2) ∨ p5)) ∨ ((p3 ∧ False) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156917690859715180186072513778 : (((((p1 ∧ ((p4 ∨ p4) → p1)) → (False ∨ (p5 ∨ (p4 ∨ ((p2 ∧ False) ∨ True))))) → p4) ∨ p2) ∨ ((p5 → p5) → (False → (p4 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204349650064186697697492049037 : (((False ∨ ((p5 → True) ∨ True)) ∧ False) ∨ ((p2 ∧ ((((p1 → p5) → p4) → p3) ∨ True)) ∨ (((p1 ∨ p4) ∧ (p5 → p5)) ∨ (p4 → True)))) := by
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
theorem thm_5_vars_686210623039274222606875962454 : (((((p4 ∨ (p2 ∧ ((p5 → ((p2 → p5) ∨ p2)) ∧ p2))) ∨ ((p1 ∧ p4) ∨ (p5 ∧ p4))) → (((p4 ∨ False) ∧ p3) ∧ (p5 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624023419446325618690075496713 : ((((p2 ∨ (((False ∧ (True ∨ ((p2 → ((True ∨ (p3 → True)) ∨ p1)) ∨ (p4 ∧ p3)))) → (p1 → p1)) → (p3 ∨ (p3 ∧ False)))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_117334593182986136475534292162 : ((False ∧ ((p3 ∧ (True ∨ p4)) ∨ ((False ∨ (((p1 ∧ ((((p5 → p3) ∧ (p5 → True)) ∨ p5) ∨ False)) → p5) ∧ p3)) → p5))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336370433762072168202404452752 : (p1 → (((p2 → True) → (((p4 ∨ (p2 ∧ False)) ∨ (p1 ∨ ((((p5 ∨ True) → p2) ∨ True) ∨ ((p4 → (p1 ∧ p5)) ∨ False)))) → p5)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42959289167257311494326283953 : (((p5 → (((p1 ∨ ((p5 → (True ∨ ((p2 ∧ (p4 ∧ (p1 ∨ True))) → (False ∨ False)))) → (p3 ∨ p4))) ∨ (p5 ∨ True)) ∧ p3)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136037695983719098539058934832 : (((p2 ∧ ((p2 ∧ p4) ∨ ((p1 ∨ (p1 → p5)) → p4))) → (((((p3 → (p5 → p5)) → p1) ∧ False) ∨ p2) ∨ p5)) ∨ (p1 ∧ (p2 → True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245454854915266732889929821945 : ((p2 ∧ p4) ∨ (p3 → (((p4 ∨ (False ∧ p2)) ∧ p1) ∨ ((p2 ∧ (p2 ∧ ((((p2 → p4) ∨ p1) ∨ (p5 ∨ False)) → (p5 ∨ p2)))) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244945862324864428325118044664 : ((p1 ∧ p3) ∨ ((p3 ∧ ((p1 ∨ False) ∧ p3)) ∨ (((p4 ∧ False) → ((False ∧ (((p5 → p1) ∧ False) → (p3 ∨ p1))) ∨ True)) ∨ (True → True)))) := by
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
theorem thm_5_vars_65869351691300178796580657957 : ((p4 ∨ ((p4 ∧ p5) ∨ ((((((p1 ∧ p2) ∨ (((p1 ∧ True) ∨ p1) ∨ p3)) ∧ p4) ∨ ((True → (p2 ∧ p1)) → p4)) → p2) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689899862739356286409687684410 : (((((True ∨ False) → (((True ∧ ((p4 ∨ p5) ∨ p4)) → (False → p4)) ∧ (True → p5))) ∨ ((((p1 ∨ p5) → False) ∨ p1) ∧ (p3 → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228942587188936041836067107995 : ((p4 ∨ (p5 ∨ p1)) ∨ (((p1 ∧ p4) → ((p5 ∨ (p5 ∧ (p3 ∧ p5))) ∨ p1)) ∨ (((True → True) ∧ p3) → ((False ∧ p4) ∨ (p2 → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615196742641620496455263296831 : ((((((p5 ∨ (p3 ∨ p3)) ∨ (True ∧ (((False ∧ True) ∨ False) → (p3 ∨ (False → p4))))) ∧ (((False ∧ False) ∨ (p2 → p2)) ∨ p1)) ∨ p2) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695793579054354952460252904829 : (((((p5 → (p3 ∨ p1)) ∨ ((p2 → (False ∨ p5)) ∨ ((False ∧ p5) ∧ True))) → (True → ((p2 ∨ (p4 → (True → (p2 → p4)))) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50451220078620073127100808733 : (((p2 ∨ (p5 → ((((True ∨ False) ∧ (((p1 ∧ True) ∨ (p4 ∧ p1)) ∨ False)) ∨ p3) ∨ (False ∨ True)))) ∨ (False ∧ ((False → False) ∧ False))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711205569922681492208451485038 : ((((p3 ∧ (p4 ∧ ((p1 ∨ p4) → p2))) ∧ (p2 ∧ (((p4 → (p5 ∧ p1)) ∨ (p3 ∨ (((p1 ∨ p1) → (p5 → p1)) ∨ True))) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225850841729080545566299695413 : (((False ∧ p1) ∨ p2) ∨ ((p3 ∨ p5) → ((p4 → True) → (((p1 ∨ p1) → (True → p4)) ∨ (p2 → (p1 → (((p5 → p5) ∨ True) ∧ p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62720397235614855623920673696 : ((p4 ∧ ((True → (p3 ∨ (((False ∧ (p2 ∧ ((p3 ∧ True) ∨ p5))) ∧ p1) → (p4 ∧ ((True → p1) ∧ ((p5 ∧ p2) ∨ p2)))))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694744327934635115469641472541 : ((((p4 ∨ ((True → ((p5 → ((p4 → True) ∨ p4)) ∧ (p1 ∨ p5))) ∨ p5)) ∨ (p5 ∨ ((p1 ∨ ((True ∧ p4) → p4)) ∨ (p1 → p2)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179250713040370801061172113908 : ((p5 ∧ ((p5 ∧ (True → False)) → (p5 → (p4 ∨ (p3 ∨ (p5 ∨ False)))))) ∨ (((p2 ∨ False) ∨ p5) → (p1 ∨ ((True → (False → p2)) → True)))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769120129990819711169489278085 : (((p5 ∧ ((p5 ∧ p3) ∧ ((p5 → False) ∧ (((((p4 → ((True ∧ p4) ∨ False)) ∧ p5) ∨ True) → ((False ∨ p4) ∨ False)) → (False ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137236384970442019468697399874 : ((p1 ∧ ((((False → p3) ∨ (False ∧ p3)) → ((p2 → p2) ∧ ((p5 ∨ p3) → (p5 → (p5 ∨ p5))))) → (False ∨ p3))) ∨ ((p3 ∨ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258184925954299257015723729917 : ((p4 ∨ p4) → ((p2 ∧ ((True → True) → p2)) ∨ (((p4 ∧ (p1 ∨ True)) ∨ (True ∨ ((p3 → (False ∧ p5)) → p4))) → ((p4 ∧ p3) → p3)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h6
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Implications on the right can always be decomposed.
    intro h17
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h24 =>
        -- One of the premise coincides with the conclusion.
        exact h19
    case inr h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h27 =>
        -- One of the premise coincides with the conclusion.
        exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114731221247636453436974342292 : (((((False → p2) → ((False ∨ False) → p1)) ∧ (p1 ∧ (p1 ∨ ((True ∨ p1) → True)))) → (p1 ∧ (p4 → ((p2 ∨ p3) ∨ True)))) ∨ (True → p2)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53516267243482069790089623143 : (((False → (((False ∧ p1) → (p4 → ((p3 ∨ False) → p4))) ∨ p3)) → (((p5 ∨ p5) → (p5 ∧ (p5 ∧ (p1 → p4)))) ∨ (p1 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137176633103897730025091717604 : ((False ∧ (((((p1 ∨ ((True ∨ p2) ∧ p1)) → p4) → p4) → (p3 → p1)) ∧ ((p4 ∨ (True → p5)) ∨ (p3 ∨ False)))) ∨ (p4 → (p4 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216333432407757556666926602207 : ((p2 → (p1 → (p3 ∧ p2))) ∨ (((p5 ∧ (False ∧ (False ∨ (p2 ∨ True)))) ∨ (False ∧ (True ∧ p5))) ∨ ((p1 ∧ False) ∨ ((False ∧ p1) → False)))) := by
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
theorem thm_5_vars_119288459095977910741616122730 : ((p3 → ((p3 ∧ ((p2 ∧ (p5 ∧ (p5 → p2))) ∨ (p4 ∨ ((True → (((p5 ∧ (p2 ∧ p1)) ∧ True) ∨ p4)) ∨ p4)))) ∨ p1)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136403582953676514417962055633 : (((True → (p1 ∨ (False ∧ p2))) ∨ ((p5 ∨ (p5 ∧ (True ∧ (p3 → (p5 → (p2 ∨ (p2 ∧ True))))))) ∨ (p5 → p5))) ∨ (p5 ∨ (p1 ∧ p2))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41777578700173320360955565659 : ((((((p3 ∧ p4) ∧ p4) ∧ p4) → (p2 ∨ (p5 ∧ (((p2 ∨ p5) ∧ (p1 → (((p4 ∧ (p2 ∧ False)) ∧ True) → p1))) → p4)))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172440519326072342966117762815 : ((((p2 ∨ (False ∨ True)) ∧ p5) ∨ ((p4 ∧ (p1 ∧ ((p3 ∨ p2) ∨ p5))) ∨ p3)) ∨ (p3 → ((False ∨ (True ∨ p5)) ∨ (p5 → (p2 → p3))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304819301528714360194550807275 : (p1 ∨ (((((p5 ∧ p2) ∨ p2) ∨ ((p2 ∨ (((p3 → ((p5 → p2) ∨ ((p4 ∨ p2) ∨ p4))) ∧ False) → p2)) ∨ p4)) → False) → (p4 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p5 ∧ p2) ∨ p2) ∨ ((p2 ∨ (((p3 → ((p5 → p2) ∨ ((p4 ∨ p2) ∨ p4))) ∧ False) → p2)) ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260248198479050519124032883834 : ((p2 → p3) → (((True ∧ ((p3 ∧ True) → p2)) ∧ True) → ((True ∧ (p4 → (((p2 ∨ p1) → (True → ((True → p5) ∧ p4))) ∨ p4))) ∨ p1))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186205046527482652235238508267 : (((p3 ∨ ((((False → True) ∨ p2) ∧ False) ∨ (p2 ∧ p2))) ∨ False) → ((((p4 ∨ p5) ∨ ((p4 ∨ (True → True)) ∨ True)) ∨ (p2 ∨ True)) ∨ p4)) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h8 =>
          -- False on the left can always be used.
          apply False.elim h7
        case inr h9 =>
          -- False on the left can always be used.
          apply False.elim h7
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134845693066662568391945500668 : (((p4 ∨ ((((p4 ∧ (False ∨ False)) → False) ∨ (p3 ∨ p1)) ∨ (p5 ∧ (p4 ∨ (p1 ∧ (p4 ∧ (p3 ∨ p4))))))) → p4) ∨ (p3 ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41829442521582497629317767603 : (((((p3 → p1) → False) ∧ (False ∧ ((p5 ∨ p3) ∨ (((False → ((p2 → p3) ∧ (True ∨ p3))) ∨ p1) → ((p1 ∧ p5) ∨ p5))))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619330162859171620637609750355 : ((((((p3 → p4) ∨ True) → ((((p5 → p4) ∨ (True → (True ∨ (p3 → True)))) ∧ (p1 ∨ (p4 → p1))) ∧ ((p5 ∧ True) → p1))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45518719786757012770025409260 : (((p1 ∨ ((True → (((((p1 ∧ (p1 → p2)) ∨ False) ∧ p5) ∧ (False → p4)) ∨ p5)) ∨ (((p1 ∧ p1) ∨ False) ∨ (False → p1)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670797879587537995168780003267 : ((((p1 ∧ ((p3 ∧ ((p5 ∧ (((p2 → False) ∨ True) → True)) ∧ (((True ∨ (True ∧ True)) ∧ p4) → p2))) → p2)) ∨ (True ∨ (p4 ∨ p3))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_157531267981447163034654977352 : ((((((p5 → p4) ∧ (p5 ∨ (False ∨ p4))) ∧ (p5 → (p4 → (p4 → p3)))) ∧ p3) → (p1 → p2)) ∨ (p2 → ((p2 ∧ (True ∨ p5)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165636824252535097140379753181 : (((p1 ∧ (p1 ∧ ((False ∧ p5) ∨ False))) ∧ (p4 ∧ (((p2 ∨ p1) ∨ p3) ∧ (p3 ∨ p1)))) ∨ ((p5 → (p2 ∨ ((p4 → p5) ∨ p5))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611949072063729954922694894995 : ((((((p1 → (((p4 ∨ p2) ∨ ((((p4 → p2) ∨ False) ∨ (True ∧ (False → p5))) ∧ p1)) → (p5 → p2))) ∧ p2) ∧ (p3 → p2)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50373870650560490354704111998 : ((((p1 ∨ (p4 → p4)) → (p1 ∧ ((p4 ∧ ((p3 ∨ p4) ∧ ((p1 ∧ p3) ∧ (p2 ∨ p5)))) ∨ p1))) ∨ ((False → p4) → (True ∨ p3))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614118328231515383479627937457 : (((((p2 → ((True → p4) → ((((True ∧ p4) ∨ p3) → (((p5 → False) ∧ (False ∨ p1)) ∧ p4)) ∧ True))) ∨ (False ∧ (p4 ∨ p4))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786100289018666802264576807028 : (((p4 ∨ ((((((True ∧ ((p2 ∧ p4) ∨ ((p5 ∧ False) ∧ False))) → p3) ∨ (True ∧ False)) → (p5 → p4)) → p2) ∧ (True ∧ (p5 ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780562571325537413684935285538 : (((p2 ∨ ((True ∧ ((True → p1) → ((False ∧ ((p3 ∨ p5) ∨ p5)) → p3))) → ((p1 ∨ (False ∨ (True ∧ False))) ∧ ((False → p4) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46114745548442413159678763028 : ((((False ∨ (False ∧ ((((((p5 ∨ (p3 ∨ (p3 ∧ (p2 ∨ p4)))) ∨ p3) ∧ False) → p4) ∨ (True ∧ p5)) → False))) ∨ True) ∧ (p4 → True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50812060185333785415164897173 : (((p3 → ((True ∨ (p2 ∧ p2)) ∧ (((p2 ∧ False) → p5) ∨ (p1 ∧ ((p1 ∧ (p1 ∧ p1)) → p2))))) → (((p1 → False) → p4) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356897955529357814680641182589 : (p5 → (((p1 ∨ (False → p3)) → p3) → ((p1 ∨ (p1 ∧ (p3 ∧ ((p2 ∨ p1) ∨ p4)))) → (((False ∨ p4) ∨ p3) ∨ (p2 → (p5 ∧ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p1 ∨ (False → p3)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40300486046390295225177729751 : ((((((((((True → p5) → p4) → (True → (p2 ∧ (p1 → p2)))) → (p1 ∨ (p5 → p4))) → (p5 → p4)) ∨ True) ∧ p4) ∨ p1) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624599377889047360507257958905 : ((((p4 ∨ (((p4 ∨ p1) ∧ (((p4 ∧ (False ∧ (p2 ∧ p1))) → p3) ∨ p1)) → (((p5 → p5) → p4) → ((p5 → p4) ∧ False)))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_184452673206648752758455845624 : (((p1 ∨ ((p5 → p4) ∨ (False ∨ (p1 ∧ p2)))) ∧ (p4 ∧ p4)) ∨ (p3 → (((p2 → ((p1 ∧ (p4 ∧ (p4 ∧ p5))) ∨ True)) ∧ p3) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645186027728952216192192031903 : ((((p3 ∨ (((p1 ∧ True) → p3) ∧ (False ∨ (((((p3 ∧ p1) ∨ False) ∨ (p1 ∨ p1)) ∧ (p4 → p2)) → (p3 ∧ (False ∨ p3)))))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197964589490028992216283899504 : (((p5 ∧ p4) ∧ ((True ∧ False) ∨ (p2 ∨ p4))) ∨ ((False ∧ p1) → (((p5 ∨ p4) ∨ (p3 ∧ (p1 ∨ p2))) ∨ (p4 ∧ ((True → True) ∧ p1))))) := by
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
theorem thm_5_vars_37940022791500775926967052080 : ((((p3 ∨ ((p1 → p4) → (((((p1 → p1) ∨ ((p5 ∨ p1) → (p1 → p2))) → p2) ∧ (p2 ∨ p1)) ∧ p4))) ∧ (False → p4)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59046973638588015868382417315 : (((p4 ∧ p3) ∨ (((p2 ∨ p2) ∨ (p5 → (((p4 → False) ∨ ((p2 ∧ p2) ∧ (False → p3))) → (True ∧ (p3 ∨ (False → False)))))) ∨ p5)) ∨ p2) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10



