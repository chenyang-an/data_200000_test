variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142440312850558906771452660978 : ((p5 ∧ (((((p2 → (p4 ∨ (p2 → False))) ∧ p1) ∧ p3) ∨ (((p1 ∨ p5) ∧ p3) ∨ (p4 ∧ (p5 → p4)))) ∧ p3)) → ((p3 → p4) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42717189178680975727367508903 : (((p5 ∨ (p4 ∨ (((((True → p1) ∧ ((p1 ∧ ((False ∧ True) ∧ p5)) ∨ (False → p1))) ∨ (p3 ∧ p2)) ∧ (p4 ∧ p1)) ∧ p1))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319389005461169738981809771449 : (p4 ∨ ((((((p5 ∨ p1) ∧ p2) → ((p4 ∨ p1) ∨ (p1 ∧ p2))) ∧ p3) ∨ p5) → (p1 ∨ ((p5 ∧ False) ∨ ((p5 ∧ (p5 ∨ p3)) → p5))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792338197487650582150735961006 : (((True → ((p2 ∨ ((((p5 → (True → (p2 → p3))) ∧ (p4 ∧ (p1 ∨ p2))) ∨ False) → p2)) → (p4 ∨ ((p1 → (p1 ∧ p3)) ∨ True)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725729596330571216442081565486 : (((((p1 ∨ p2) ∧ p4) ∨ (((((p3 ∧ (True ∨ p5)) → (((p4 ∧ False) ∨ (p4 → False)) ∧ p1)) ∨ p5) ∧ p1) ∨ ((p4 ∨ p1) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158222534428856493610935325093 : (((p5 ∧ (p5 → True)) ∧ (p2 ∧ (((p5 → (p3 → True)) ∨ True) → (((p4 → p4) → p5) → False)))) ∨ ((p2 ∧ (p2 → p4)) → (p2 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125554723628336247707603730890 : (((p1 → False) ∧ (((((True ∨ ((p5 → False) → (((p3 → False) → p4) → p2))) ∧ p1) ∨ False) ∧ p1) ∧ (p5 ∨ (False → p2)))) → (p2 ∨ True)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
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
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151193511299686478599031045638 : ((((((True ∧ p2) ∧ p5) → ((p5 ∧ False) → p3)) → (((p4 → (p3 ∨ True)) → p2) ∨ (p4 → p3))) → p4) → ((p3 ∧ p5) → (p5 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66656197155118997599316624061 : ((True → ((p5 → (((p5 ∧ (False ∧ True)) ∧ True) → p4)) ∧ ((p5 ∨ p2) ∧ ((p5 ∨ (p3 ∨ False)) ∨ (p1 → (p5 ∨ (False ∨ True))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114009494027912846761072422281 : (((((p3 ∨ p1) → (p5 ∨ ((((p4 ∨ (False ∨ True)) ∨ True) ∨ p1) ∧ (p5 → (False ∨ p5))))) ∧ p2) ∨ ((True ∧ True) ∨ p1)) ∨ (p5 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116907998963380765179241675571 : (((p5 → p3) ∨ ((p2 ∧ (p1 ∨ (False ∨ (p3 ∧ False)))) ∨ (p1 → (p1 ∧ (p5 ∧ ((p2 ∨ (p4 → p5)) ∨ (p1 ∨ p2))))))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116806058390830726242045022532 : (((p3 ∨ p1) ∨ (p4 ∧ (p1 → (((((((p1 → False) ∨ (p1 → True)) ∧ p5) ∨ (p3 ∨ (p5 ∨ False))) → p3) ∨ True) → False)))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187835954572415509403583898792 : ((p5 → ((False ∨ (p5 → ((True ∨ p5) ∨ (False → p4)))) ∧ p3)) → (p1 → (True ∧ (((False ∨ (False → p5)) ∧ ((p2 → p4) ∨ p1)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157753288778893421902639023820 : (((((p3 ∧ p5) ∨ (p1 ∨ False)) ∧ ((p3 ∨ (p1 ∨ p1)) ∨ p5)) ∧ ((False ∨ p3) ∨ (p3 → p4))) ∨ (p5 → (p4 → (p2 ∨ (p1 ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172664079768758408169624105050 : (((p1 → False) ∧ ((False ∨ (((p3 ∧ p4) ∨ p4) ∨ p4)) ∨ ((False ∨ True) ∨ p5))) ∨ (((p5 ∧ False) ∨ ((True ∨ (p1 ∧ p3)) → False)) → p5)) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (True ∨ (p1 ∧ p3)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736426984180035743346056297321 : ((((p1 → False) ∧ ((((True ∨ ((((False → p5) → p5) ∧ (True → False)) ∨ ((p5 ∧ True) → True))) ∨ p1) → p5) ∧ ((p1 ∧ p2) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174708656746674981350750621758 : (((p1 ∨ (p2 → p4)) ∨ (True ∨ (((False → p3) ∨ ((False → p5) ∨ p4)) ∧ True))) → (((p5 ∧ ((p2 ∧ p4) → p5)) ∨ p3) ∨ (True ∨ p4))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680030322559978557919630641266 : (((((False ∧ (p2 ∨ ((False → (True ∧ (p4 → (p4 ∧ ((p2 ∨ p2) ∧ p1))))) ∧ (False ∧ p5)))) → p4) → (False ∧ (p3 ∨ (p4 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168605983464902738628111313653 : ((p3 ∧ (((((p4 ∨ (p2 → True)) → p3) → (p4 ∨ False)) → ((p3 ∧ p5) ∨ p1)) → p4)) → (((p2 → p4) ∨ (True ∧ p1)) ∨ (p5 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54273124225026168854434844781 : ((((p1 → (p3 → p4)) ∧ ((True → True) → p4)) ∧ ((p5 ∨ (((p4 ∧ False) ∧ (True → p1)) → (p5 → ((p1 ∧ p4) ∧ True)))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148635414960048241767084150264 : (((p3 → ((p1 → ((False → (p1 → p1)) → p2)) ∨ p4)) → ((((p5 ∧ True) ∨ p5) → p2) ∨ (p5 ∧ p5))) ∨ (p5 → ((p1 ∧ p2) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_34436868433326914870835799258 : ((True → (p2 ∨ (((p5 → False) ∧ False) ∨ ((((((False → p5) ∧ (p4 ∧ p3)) → p2) ∨ p1) ∨ p3) ∨ (p4 ∨ (False ∨ (True ∨ p1))))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166184171701844693269850841011 : ((p1 ∧ ((p3 ∧ (((p5 ∧ ((False → p5) ∧ (p5 ∨ (False → False)))) ∨ p3) ∨ p3)) ∨ p4)) ∨ (p2 ∨ (p2 → ((p4 → (p3 → True)) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134750389738573398278781448618 : ((((p4 ∨ p3) ∨ (((p4 ∧ (((((True ∨ (p2 → p2)) ∧ p1) ∧ p4) ∧ (p4 ∨ False)) ∨ False)) ∧ p1) → p3)) → p4) ∨ ((p5 ∧ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114537401084436934003026364514 : (((p1 → (p1 ∨ (((((p2 ∨ (False ∨ False)) → p5) ∧ (p2 → p4)) → False) ∧ (p5 ∧ p5)))) → ((p4 ∨ (False ∧ p1)) ∧ p4)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341015758604828559043275062032 : (p2 → ((p2 ∧ ((p1 ∧ ((p3 → p3) ∧ p1)) → (((p4 ∧ ((p4 → (((True ∧ (False → False)) ∧ p1) ∨ p3)) ∨ p3)) → False) ∨ p2))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309869916356808292292305805356 : (p2 ∨ ((p5 → ((p4 → ((p5 ∨ p1) ∨ (False → p4))) ∧ (((False ∧ (p5 → p1)) ∨ (False → p3)) ∨ True))) → ((p4 → False) ∨ (p1 ∨ True)))) := by
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
theorem thm_5_vars_748446121712118964239354626188 : ((((p2 → p4) → ((True → p5) → ((((((p2 ∧ p1) → True) ∨ p3) → ((p5 → (p4 ∨ p3)) → (p1 ∧ p5))) ∨ False) → (p4 ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45514073258655996253489535487 : (((p1 ∨ (((((False → p2) ∧ (((p1 ∧ (False ∧ True)) ∧ ((p3 ∨ p4) ∨ p3)) ∧ True)) ∨ (p5 ∨ False)) ∨ True) → (p3 ∨ True))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206618182731057008070927419568 : ((p1 → (((p4 → p3) → True) ∧ p2)) ∨ ((((p3 ∧ p2) ∨ (p5 ∧ p4)) ∧ ((p5 ∧ (False ∧ (False ∨ (True ∨ (p4 ∧ p2))))) ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172659050262377784149910239444 : (((True → p2) ∧ (False ∧ ((((p4 ∨ (False ∧ p5)) → (p3 ∧ True)) ∨ p5) → p1))) ∨ (True ∨ (p1 ∧ (((False → True) ∧ p5) ∧ (p1 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156786009061239770090299404949 : (((p1 ∧ ((p2 ∧ ((p2 ∨ ((False → p4) → p4)) ∧ (p3 ∧ p2))) ∧ (p2 ∧ (p4 ∨ True)))) ∧ p2) ∨ (p3 ∨ ((p5 ∨ (p3 ∧ p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761613819600587232122461519027 : (((p3 ∧ (((((((p2 ∧ True) ∧ p1) → False) → ((p1 ∨ ((True ∧ p5) ∧ p4)) ∧ False)) ∨ True) ∧ (((True ∨ p3) → False) ∧ p5)) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711520164480999105678733245791 : ((((True → (p2 ∨ (True ∨ (p5 ∧ p4)))) ∧ (p2 → (((True ∧ False) ∨ (p4 ∧ (p1 → (True ∧ (p4 ∨ p5))))) ∨ (p4 → (True → p4))))) ∨ p5) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136368657809557109937420231936 : ((((p2 ∨ (p4 → p3)) ∨ False) ∨ (p3 → (p1 ∨ (((p1 ∨ ((p2 ∧ True) ∧ p3)) → (p4 ∨ (p4 → p2))) → p4)))) ∨ ((False ∧ p1) → p4)) := by
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
theorem thm_5_vars_116380543118037064248014152810 : ((((p3 → True) → p3) → ((p2 ∨ ((p1 → ((p5 ∨ (p4 → False)) ∨ True)) → p1)) ∨ ((((False → p4) → p4) ∨ p3) → p3))) ∨ (p2 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (p3 → True) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h4
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352819579612812493079989311634 : (p4 → ((True → p1) → ((((p3 ∨ (((p4 → True) → ((False → (True → True)) ∧ (p4 ∧ True))) → False)) ∧ (p2 → (p4 ∧ p1))) ∨ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341229730131580057641599174989 : (p2 → (((p2 → ((p2 → ((False ∨ (p5 → p5)) ∧ (((p2 → (p5 ∧ (((p3 ∧ p1) → True) ∨ p1))) ∨ p2) → p4))) ∨ True)) → False) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p2 → ((p2 → ((False ∨ (p5 → p5)) ∧ (((p2 → (p5 ∧ (((p3 ∧ p1) → True) ∨ p1))) ∨ p2) → p4))) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355581898828242188678752000461 : (p5 → ((((p1 ∧ (((((p1 ∨ p2) ∧ p1) → p3) → p2) ∨ p5)) ∨ p1) ∨ (p5 → (((p1 ∧ (p2 ∨ True)) ∧ p3) ∧ p4))) ∨ (p2 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178169839713666410195601907824 : ((((False ∧ p5) → (((p3 → False) ∧ p1) → (True → (p3 ∧ p4)))) → p5) ∨ (p1 ∨ (((False ∧ (p4 ∧ (p3 ∨ p5))) → (p2 ∨ p4)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192537152005204838394515815096 : (((p1 ∧ (p1 → ((p1 ∨ True) ∨ (p3 ∧ False)))) ∨ False) → ((p3 ∧ (((True → p4) ∧ p4) ∧ False)) ∨ (((p2 → p1) → p2) ∨ (False → p2)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22043246746684235437465665754 : (((((False → p5) ∧ (False ∨ (p4 ∧ p1))) ∧ p5) ∨ ((p1 ∧ ((True ∧ (((p2 ∨ True) ∨ p2) ∨ ((True → p5) → p4))) → p4)) ∨ True)) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47028809439475467189203200834 : ((((p3 → ((p5 ∧ True) ∨ (p3 → (((True ∧ (p4 → p3)) ∨ ((True ∨ (p2 → p2)) → True)) → (False ∨ p4))))) → p3) ∨ (p1 → p1)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603837449985186866573907913613 : ((((p4 ∨ (True ∧ (p5 → ((((p2 ∧ p3) ∧ False) → (((False ∧ p4) ∧ p1) ∧ (p2 ∧ (False ∨ True)))) → ((True ∧ p4) → p2))))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628107352170060626681432124930 : (((((((True → p1) → p2) ∧ (((p5 ∧ (p1 ∧ p4)) ∨ ((True → (p2 ∨ p4)) → ((False ∧ True) ∨ (False → True)))) ∨ p4)) ∧ p1) → p2) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h12 : (True → p1) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h14 := h4 h12
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h16 : (True → p1) := by
        -- Implications on the right can always be decomposed.
        intro h17
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h18 := h4 h16
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h19 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h20 : (True → p1) := by
      -- Implications on the right can always be decomposed.
      intro h21
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h22 := h4 h20
    -- One of the premise coincides with the conclusion.
    exact h22
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65215023163369675668104226527 : ((p3 ∨ (((p4 ∨ ((((False → p3) → p3) ∧ False) ∨ (p1 → p1))) ∧ ((p3 → (((p1 ∧ (p1 → False)) → p4) ∨ p2)) ∨ p3)) ∨ False)) ∨ p3) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178288336088416381725993647069 : (((p5 ∧ (p5 ∧ ((p2 ∨ ((p3 ∨ p5) → p2)) → p3))) ∧ (p4 → True)) ∨ (p5 ∨ ((p1 ∧ (p2 ∧ (p4 ∧ p4))) ∨ ((True ∨ p2) ∨ True)))) := by
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
theorem thm_5_vars_200853852965502995018630212441 : ((True ∨ ((p4 ∧ p5) → ((True → p2) ∨ p4))) → (((p3 ∨ p4) ∧ False) ∨ ((p1 → (p2 ∨ (True → (False ∧ (p2 ∧ True))))) ∨ (False → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600257748424938515521095689707 : (((((p3 → False) → ((True ∧ (p3 ∧ p1)) ∧ ((((((p5 ∧ p2) → (False ∨ p2)) ∨ True) → (p2 ∨ (p3 ∧ p4))) ∨ p3) → p3))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622950399522505726534184208292 : ((((p5 ∧ ((((p5 → True) ∨ p4) → ((True ∧ p3) ∧ (p2 → p2))) ∨ (((((p3 → p2) ∨ p5) ∨ p2) → False) ∧ (p3 → p2)))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_263080710535641981297781104186 : (True ∧ ((((((((p2 ∨ p3) ∧ p3) ∧ (False ∧ True)) ∨ (p1 ∨ (p2 ∨ p4))) ∧ p4) ∨ (True ∨ ((False ∧ p2) → p3))) ∨ p1) ∨ (p1 ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49233000451258964038292426369 : ((((p1 → p4) ∨ (((False ∨ p3) ∨ p3) ∧ (True ∧ ((((True ∨ True) ∨ p5) ∨ (False → p2)) ∧ (p3 ∧ p1))))) ∨ ((p2 ∧ p1) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349264288038958037840132360940 : (p3 → (p1 → (p3 → ((((p5 → (p5 → ((((True ∨ (p5 ∧ p3)) ∧ ((p1 ∨ (p2 → p1)) ∧ p4)) → p2) ∧ p1))) ∨ False) → p2) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118813177723025949667859255619 : ((True → ((((p5 ∨ (True ∨ (p4 ∧ True))) ∧ (False ∨ p1)) ∨ ((False → p5) ∧ (((False ∨ p2) ∨ p2) ∧ (p2 ∧ False)))) ∨ p4)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340305630232697041106689603475 : (p2 → ((((p3 ∧ (((p5 → p5) → (((p1 → True) ∨ (p1 → (p2 → (p2 ∨ p3)))) → ((p2 → p1) ∨ p2))) ∧ p5)) ∧ p5) ∨ p2) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354930646916742167183185410459 : (p5 → ((p3 ∨ (True ∧ ((((p2 ∨ (p2 ∧ p4)) ∨ p1) → p4) ∨ ((p3 → (p1 ∨ p4)) → (True ∧ ((False ∨ p1) ∧ (p4 ∧ True))))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809840859045628796517303236141 : (((p5 → (((p2 → (((p2 ∨ p5) → False) ∨ ((p5 ∨ p1) ∧ (((p2 → True) ∧ ((p2 ∧ p5) ∧ p2)) ∧ p3)))) → p1) → (False ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40731136412396407062231641199 : ((((((False ∨ (False → False)) ∧ p1) ∨ (p2 → ((p4 → (p5 → p1)) ∨ ((((p1 ∧ p4) ∧ (p5 ∨ False)) → p1) ∨ p3)))) → p3) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172027604963279411873773438715 : ((((p5 ∧ p4) → ((p1 ∨ False) ∧ (p1 ∨ ((p1 ∨ True) ∨ False)))) ∨ (p4 → p2)) ∨ ((True → (((p4 ∧ True) → p4) ∧ False)) → (p5 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110924431933901160842765903995 : ((((p3 → (((((p4 ∧ p1) → p5) → p5) ∨ (False ∧ ((((p4 → p4) ∨ p1) ∧ p1) → (p2 ∨ True)))) → p5)) → p3) ∧ p3) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790404556604008213972234493769 : (((p5 ∨ (p5 ∧ ((p5 → (p4 ∨ (True → (((False ∧ (p2 → p1)) ∧ (((((p3 ∨ False) ∧ True) ∧ p2) ∨ True) ∨ p2)) → p4)))) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606669510918170412947718531537 : (((((((p1 → (True ∧ (p5 ∨ ((((p3 ∨ (p5 → p3)) → p1) ∧ (True ∧ (p1 ∨ True))) → False)))) → p2) ∧ (p3 → False)) ∧ p4) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_228421987511795071051580575463 : ((False ∨ (p3 ∧ p4)) ∨ (((p3 ∨ ((False ∧ ((p3 → ((p2 → p2) → (p2 ∧ False))) ∧ p1)) ∨ p2)) ∧ p2) → (p5 ∨ (p2 ∨ (p2 → p4))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43952720900602985189747934227 : (((((p2 ∧ p2) ∨ (True ∧ ((p1 ∨ p5) → ((p1 ∧ (False ∨ ((p4 → p2) → p5))) → (p5 → (p3 ∨ p5)))))) ∨ (p5 ∨ True)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729910222269278360624141257710 : (((((p3 ∧ True) → p4) → (((((p4 → (p5 ∧ False)) ∧ (True ∧ True)) ∨ p5) ∧ ((p5 ∧ p3) → ((p3 ∧ p5) ∧ (p4 ∧ True)))) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_143221244825311277269104674637 : ((p2 → (p2 ∨ (((True ∧ p4) → ((((p5 → p3) ∨ p3) ∧ ((False ∨ (p3 → p1)) → p4)) ∨ p1)) ∧ (p4 → p5)))) → ((p3 ∨ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135283244505082658663924535024 : (((p1 → ((p1 ∧ (True ∧ p2)) ∧ (p5 ∧ ((p4 → (p2 ∧ p1)) → (False → ((p2 → p4) → p3)))))) → (p3 ∨ p4)) ∨ (False → (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769399752657340422852756734296 : (((p5 ∧ (False ∧ (p1 ∨ ((((((False ∨ p4) → (p2 → (True → False))) ∧ p3) → False) ∨ True) ∨ (p3 ∧ (((p3 → p4) ∨ p2) ∨ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181199905726217101647784285495 : ((p2 ∧ (((((True → ((p2 ∨ p2) ∧ p1)) → p4) ∨ True) ∨ p1) → p1)) → ((False ∨ (p3 ∧ (True ∧ (((p4 ∨ False) → False) ∧ False)))) ∨ True)) := by
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
theorem thm_5_vars_147558774540973048464439503415 : ((((((p4 ∧ ((True ∨ ((((p5 ∨ p1) ∧ True) → p4) ∨ (p2 ∧ p4))) → p2)) → p3) ∨ p2) ∧ p2) → p1) ∨ (((p3 ∨ p2) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667884464921897902689635619869 : ((((p1 ∨ (p2 ∧ ((((p3 ∨ (p3 ∨ (p4 → p2))) ∨ (p2 ∨ p2)) ∨ ((p5 ∧ p3) ∨ True)) ∨ (False ∨ False)))) ∧ (False → (p5 ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303795304117305406300520794623 : (p1 ∨ ((((((True → (p1 ∧ (((p4 → (p1 ∧ (False ∧ p4))) → (p4 ∧ p2)) ∨ p2))) ∨ p1) → (False → True)) ∨ (False → p3)) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305542294202373319788642479534 : (p1 ∨ ((p2 ∨ (p1 ∧ ((((True ∨ p2) → p2) ∨ p5) ∨ (True ∧ (p2 ∧ p2))))) → ((p2 ∧ (p4 ∧ (p3 → (p2 ∨ (p4 ∨ False))))) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
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
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255253135954346067979833338246 : ((p4 ∧ p5) → (((p2 ∧ ((p4 ∧ True) ∨ ((p4 ∧ (((True ∧ ((p1 ∨ p2) ∧ p4)) ∧ (p2 → p1)) ∨ p2)) ∧ p4))) → False) ∨ (True ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722250043557042711607840086920 : (((((True ∧ False) ∧ p3) ∧ ((False ∨ (p4 ∨ (False ∨ (p5 ∨ ((p1 → p1) → ((p3 ∨ False) ∨ p4)))))) → (((p2 ∨ p1) ∨ p1) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67555218915995435376170961220 : ((p1 → ((p2 → (p4 → p5)) → (((((p4 ∨ p3) → ((p1 → p5) ∧ False)) ∧ (False ∨ True)) → (p3 ∨ (p2 ∨ (p2 ∧ True)))) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149087352020334321468476531521 : (((p1 ∧ (p3 ∨ p3)) → (((False ∨ p2) ∨ (p5 ∨ (p3 ∧ ((p3 ∧ p2) ∧ (p2 ∨ (p3 ∨ p2)))))) → p5)) ∨ ((True ∧ (p3 ∧ False)) → p3)) := by
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
theorem thm_5_vars_53445764053656098816482055055 : ((((p1 → (p2 ∨ p4)) ∨ ((p3 ∨ p5) → ((p2 → p1) ∨ p3))) → (p5 ∧ (((p5 ∧ ((p3 ∧ p3) → True)) → (False ∧ p3)) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196925658567547840288550373304 : ((((True ∧ (False ∨ (False ∧ p5))) ∧ p3) ∨ p5) ∨ ((p3 → ((p3 ∨ False) ∨ (p4 ∨ ((p3 → p4) ∧ ((True ∨ (p1 → p5)) ∨ False))))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339632508344056964545963004056 : (p1 → (p2 ∨ ((p1 ∨ (True ∧ p1)) ∧ ((((((((p3 ∧ p3) ∨ p5) ∨ p2) → ((True ∧ p3) ∨ (p4 ∧ p1))) ∨ p3) → False) → False) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158450875489317728188898085265 : (((p5 ∨ p2) ∨ (((True ∧ p4) ∨ (((p4 ∧ (p1 → True)) → p1) ∧ (True → p2))) ∨ (p5 → True))) ∨ ((p5 ∧ ((p2 ∧ p3) → p1)) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234801834776287891540058686830 : ((p5 → (p4 ∧ p1)) → ((((p5 ∨ p1) → (((((p1 ∧ p5) ∨ False) ∧ p3) ∧ p3) → p4)) → False) ∨ ((p5 ∧ p4) → ((p2 → p3) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117236671155841316059862188931 : ((True ∧ (p4 ∧ ((((p4 ∨ (((True ∨ (True ∧ p3)) ∧ (True → p2)) → p3)) ∧ p5) → ((p3 → p2) → p4)) ∧ (p4 → True)))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118099472575245076773433063693 : ((False ∨ ((((((p5 ∧ p5) ∨ True) ∧ ((p4 → ((p1 → p1) ∧ False)) ∧ p4)) ∨ ((p5 → (p1 ∧ True)) → False)) ∧ p1) ∨ True)) ∨ (p3 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65957878999807459484523911284 : ((p4 ∨ (p4 ∨ ((True → (p1 ∨ (p1 ∧ ((p1 ∨ p1) ∧ ((False → (p4 ∨ True)) ∨ (p1 ∧ (p4 ∨ p5))))))) ∧ ((False ∨ False) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146930493823361225608192689995 : ((((p2 → (((p4 → p1) ∨ (p2 ∧ (p2 ∧ (p1 → p1)))) → (False ∨ ((p5 → p4) ∧ p5)))) ∧ p1) ∧ p1) ∨ (((p1 → p1) ∨ False) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207024239983744577920286488952 : ((((False ∧ True) → (p4 ∧ True)) ∧ True) → ((False ∨ (p4 → ((p4 ∧ ((p1 → False) → p1)) ∨ (p5 ∧ p2)))) ∨ ((p4 ∨ (False ∧ p5)) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303245140065254995004698523726 : (False ∨ (p5 → (((((p5 ∨ p3) → p3) → ((p4 ∨ (p4 → True)) → ((True ∨ False) ∨ p2))) → False) ∨ (p4 → (((p1 → p3) → p4) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_252076243443651182961636758260 : ((p4 → p1) ∨ (p5 → (p4 ∨ (((p2 ∨ ((((True ∨ (((p5 ∧ p4) → False) ∧ ((p2 ∧ True) ∨ p5))) ∧ p4) ∧ p4) → p1)) → p2) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208934233064791641240257114971 : ((p5 ∧ (p4 ∨ ((False → p5) → p2))) → ((((p2 → p2) → p4) → ((p3 ∨ (((p2 ∧ p4) → False) → (p1 ∨ p1))) ∧ p4)) ∨ (p4 ∨ True))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200866724557541942565284970092 : ((True ∨ (p3 → ((p3 ∨ (p3 ∧ p2)) ∨ p2))) → ((p2 → ((False ∨ (((True ∨ False) ∧ p1) ∨ p4)) ∨ True)) ∧ (False ∨ ((True → p4) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811302918277218584215337410015 : (((p5 → (False ∨ ((((p4 ∧ ((False ∨ False) ∨ (p1 ∧ ((True ∧ p2) ∧ (((p5 ∧ p2) → p1) → (p4 → p2)))))) ∧ p1) ∨ p3) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587106629799161712387701879773 : (((((p1 → (False ∨ (p2 → (((p5 → (((p3 ∨ p2) ∨ p4) ∧ (p1 → False))) ∧ p3) ∧ ((p3 ∧ (p2 ∧ False)) → p3))))) ∧ p2) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311901771764304418685100830686 : (p2 ∨ (p2 ∨ (True ∧ (p4 → (True ∧ ((((p2 ∧ ((True → (True ∧ p1)) ∧ p2)) ∧ False) ∨ p4) ∧ ((True → p2) → (p3 ∨ (p3 → p2))))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339785892417735027445209468433 : (p1 → (p5 ∨ ((((True → (p4 → (p5 ∧ (p2 → False)))) ∨ ((True ∧ p5) ∧ p1)) ∨ (((p2 ∧ (p4 → p1)) ∨ p3) ∨ (p1 ∨ p2))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679806634618901360965385652045 : ((((((p5 → p3) → (False ∧ ((p1 ∨ (((True ∧ p3) ∧ p3) ∧ False)) ∧ (p1 → (True ∨ True))))) ∨ p2) → ((p4 → p4) → (False ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56325154988869280140235726286 : ((((p3 → (p3 ∧ True)) ∧ p2) → ((((((p2 → p3) ∧ p1) → (p1 → p5)) ∧ p3) ∨ p1) ∨ ((((p2 ∧ p1) → p1) ∨ False) ∨ p1))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200233067342128192655587192715 : ((((p2 ∨ p2) ∨ p1) → (False ∧ (p3 ∧ True))) → ((p2 → ((True → (p1 ∨ (p5 ∨ p1))) → ((p4 ∨ False) ∧ (p1 → p3)))) ∨ (p1 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : ((p2 ∨ p2) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : ((p2 ∨ p2) ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341064369397290822458709331420 : (p2 → ((p4 ∨ (((p1 ∨ ((p3 → p3) → (p1 ∨ p2))) ∧ ((False → ((((p2 → p4) → (p5 ∨ True)) ∧ p3) ∧ p1)) ∧ p1)) → p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168093515891909585769470649735 : ((((True → (p1 ∨ p4)) ∨ p3) ∨ (((False ∨ (((p1 → p4) ∧ p1) ∧ True)) ∨ p5) ∧ p1)) → ((True → p5) ∨ (((False ∨ False) ∧ True) → p1))) := by
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
        apply False.elim h7
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- Conjunctions on the left can always be decomposed.
        let h23 := h21.left
        let h24 := h21.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h25
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h28 =>
          -- False on the left can always be used.
          apply False.elim h28
        case inr h29 =>
          -- False on the left can always be used.
          apply False.elim h29
    case inr h30 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h31
      -- One of the premise coincides with the conclusion.
      exact h30



