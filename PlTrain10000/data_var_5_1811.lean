variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319800677499609962701370901305 : (p4 ∨ ((p2 → (((p5 ∧ p1) ∨ p3) ∨ p3)) → (p3 ∨ ((p1 ∧ (((True ∧ p5) ∨ p3) → p1)) ∨ (False → (p2 → (p4 ∧ (p5 → p1)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180799988128004365573444381288 : ((((p3 ∨ True) ∧ p2) ∧ (((p5 ∨ False) ∧ (p2 → (True ∧ False))) → p1)) → ((((p1 ∨ p4) ∧ p2) → p5) ∨ ((p5 ∧ (p3 ∧ p4)) ∨ p2))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161740343981317865041833414533 : ((p3 ∨ (p2 ∧ (((((True ∧ False) → p1) → (p2 → p1)) → (p5 ∧ (p5 ∧ p5))) ∨ (p1 ∧ p1)))) → ((((p2 ∨ True) ∨ p1) → p1) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : ((p2 ∨ True) ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : ((p2 ∨ True) ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h10
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606938486061771376361946522299 : ((((((((p5 → p2) ∧ (((False → (p2 ∨ (p2 ∨ p1))) → (False → p5)) ∧ p1)) ∧ p4) → (False ∧ ((p1 → True) ∧ True))) ∧ True) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_346790534396280590544611270454 : (p3 → (((p5 ∨ (False ∨ p4)) → ((p5 ∨ (p4 ∨ True)) → ((True ∧ (False → p4)) → ((p5 ∨ p5) ∨ p5)))) ∨ ((p5 ∧ (p2 ∨ False)) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62107515561893585359290601516 : ((p2 ∧ (False ∨ ((((True → p5) ∨ ((((p3 → ((p1 ∧ p2) ∨ p5)) → False) ∨ (False → False)) ∨ False)) ∧ ((False ∨ p2) → p1)) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227986792269325412776935724773 : ((p3 ∧ (p3 ∨ p1)) ∨ ((False ∧ p5) ∨ ((p5 ∨ (((p3 ∨ p4) ∨ p1) → ((p5 ∧ False) → (((True ∧ p1) → (p2 ∨ p2)) ∨ p3)))) ∨ p5))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337786263598510372472490337109 : (p1 → ((((((((p3 ∨ ((p2 ∧ p1) ∨ False)) ∨ p1) → p3) ∨ p2) → p4) → True) ∧ p3) → ((p2 ∨ p1) ∧ (((p4 ∧ p5) ∧ p2) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66292650243431205562297526859 : ((p5 ∨ ((p1 ∧ p2) ∨ ((p1 ∨ (((True → p3) ∧ (((p3 ∨ p4) ∧ p2) → (((p2 → p5) ∨ p5) → (p3 ∨ p1)))) ∨ True)) ∧ True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_38629248850699991305312514849 : ((((((False → p5) ∧ p1) ∧ (False ∧ (p5 → False))) ∨ (p3 ∧ ((((True ∧ ((p1 → p4) ∧ False)) ∧ p3) → True) → (False ∨ p1)))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89333208144872491043560426233 : (((p3 ∨ (True → p3)) ∧ ((False → (p3 ∨ (p3 ∨ (p2 ∨ p3)))) ∧ (p4 → ((p3 ∨ (p1 ∧ True)) → ((p4 → p3) ∧ (p1 ∧ p1)))))) → p3) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h11 := h7 h10
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690903942256164440696533801776 : (((((True ∨ (False ∨ (True ∨ ((p2 ∧ (True ∧ p3)) → (True ∧ p4))))) ∧ (True → True)) → (False ∨ (((p2 ∨ True) → (False ∨ p3)) → p3))) ∨ p3) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (p2 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h15 : (p2 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h16 := h14 h15
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- One of the premise coincides with the conclusion.
          exact h18
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h21 : (p2 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h22 := h20 h21
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- False on the left can always be used.
          apply False.elim h23
        case inr h24 =>
          -- One of the premise coincides with the conclusion.
          exact h24
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82285680445326120669849430861 : (((((True ∧ p3) ∨ ((((p2 ∧ True) ∨ ((p2 ∨ p1) ∨ p3)) → (p5 ∨ p5)) ∨ (p1 → p2))) → False) ∧ (p2 ∧ (p1 ∨ (p4 → p5)))) → p1) := by
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
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : ((True ∧ p3) ∨ ((((p2 ∧ True) ∨ ((p2 ∨ p1) ∨ p3)) → (p5 ∨ p5)) ∨ (p1 → p2))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h8
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299176187489117996115429470330 : (False ∨ ((((((p5 → (False ∧ (((False ∧ ((True → False) ∧ True)) ∧ False) → p3))) ∧ p1) ∧ p5) ∨ ((True ∨ p3) ∧ (p5 → p2))) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118195912350741317262819176495 : ((False ∨ (True → (((True ∨ ((p4 → True) ∨ p1)) → False) ∨ ((True ∧ ((True ∨ False) ∨ p2)) ∨ ((p4 ∧ (p1 → False)) ∨ p2))))) ∨ (p2 → p1)) := by
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
theorem thm_5_vars_173243599593488896177152239275 : ((True → ((p3 → p5) ∧ (p2 → ((((p2 ∨ (p5 → True)) ∨ p4) ∧ p2) ∧ p1)))) ∨ (((((p2 → p3) ∧ p5) ∨ (p2 ∧ p2)) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213365479888087318594622869924 : (((p5 ∧ (True ∧ p2)) ∧ p2) ∨ (p4 ∨ (p5 ∨ ((((False ∧ (((p2 → (False ∧ p5)) → True) → p4)) → (p5 ∨ p3)) ∧ (p3 ∧ p4)) ∨ True)))) := by
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
theorem thm_5_vars_135430337280377658034698835131 : (((p3 ∨ (((p5 → ((p3 ∧ (True ∨ (p5 ∨ ((p3 ∧ p1) ∧ p2)))) ∨ p4)) → p5) ∧ p5)) ∨ (False ∨ (True ∨ p4))) ∨ (True ∨ (False ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156625370396430921818677370369 : ((((((p3 → p5) ∨ (((p4 ∧ ((p4 → p2) → True)) → p4) → False)) ∨ (p1 ∨ True)) ∨ True) ∧ p4) ∨ (((p5 ∨ p2) ∧ p4) → (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174387767444286788980588228342 : ((((False → p1) ∧ ((p3 → (p1 ∧ p2)) ∨ p1)) ∧ ((p3 → (p4 ∧ p3)) ∨ p1)) → ((((p5 ∨ p3) → p5) ∧ (p1 ∧ p5)) → (p2 ∨ p1))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42924229002279096443842455505 : (((p4 → (((((p1 ∨ (True ∧ p4)) ∨ False) ∧ (p5 ∧ p3)) ∧ ((((True ∨ p3) ∨ p4) → (True ∨ p1)) → (True ∧ p3))) ∨ True)) ∨ p3) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190199811564162629752359344722 : (((p3 ∨ (p3 ∨ (((p4 ∧ True) → True) → p2))) ∧ False) ∨ (((p4 ∨ p1) ∧ p3) → ((((p3 ∨ p3) ∧ (False → True)) ∨ p1) → (p5 → p3)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h1.left
      let h9 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h1.left
      let h14 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h14
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h1.left
    let h19 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h20 =>
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h21 =>
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114636018792967888380143670915 : (((((p1 → (((p4 ∨ p2) ∨ (True ∨ (p3 ∨ p4))) ∧ p5)) ∨ (p1 ∧ p1)) → p4) ∨ ((p1 ∨ (p4 ∨ (p1 → False))) → p4)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50486394015347631177111155201 : (((p3 → (p5 ∨ ((p4 ∨ (((p2 ∧ p2) → (False → (p4 ∨ p3))) ∨ True)) → ((False → p5) → p2)))) ∨ (((False → p5) → False) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116243454749955360353972123677 : ((((p4 ∨ True) → p1) ∨ ((((p5 ∧ p3) → p3) → False) ∧ (((((True ∧ (False ∧ p5)) ∨ p5) ∧ p1) → (False ∧ p2)) → p5))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156112018379572803065024082485 : ((False ∨ ((p4 ∧ (p5 ∧ ((p1 ∧ (p1 ∨ ((p1 ∧ p1) ∧ p3))) ∧ ((p5 → p5) ∨ p4)))) ∨ True)) ∧ ((False ∨ (p3 ∧ (False ∧ p5))) → True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3238080120931843505352003373 : ((p3 ∨ p2) ∨ (p5 ∨ ((((p3 ∧ (p2 → True)) → p5) ∨ ((False ∧ p1) → (((p2 → (True ∧ (p3 → p4))) → True) ∧ p4))) ∨ p4))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138167315938159946157387417246 : ((p1 → (((True → True) → (True → (((p1 → False) ∧ (p4 → p3)) ∧ (p1 ∨ p5)))) ∨ ((p5 ∨ p3) → (p4 → False)))) ∨ (False → (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177777933976623973673108435339 : (((p2 ∧ (p3 ∨ (False ∧ ((((p1 ∨ p5) ∨ p4) ∧ p2) ∨ False)))) ∧ p5) ∨ (p1 → ((False ∧ p4) → ((((p3 → True) → p4) → p4) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115271727412492505571843527240 : (((p5 ∧ ((p1 → p3) ∧ (p5 → (p1 ∨ (p2 ∨ p1))))) ∨ ((((p4 → p4) ∨ p1) ∧ (((p1 → p1) ∧ p1) ∨ p4)) ∨ True)) ∨ (p3 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146985372008995070365204678292 : ((((True ∧ ((((False → (p5 ∧ (True → p2))) → ((p5 ∧ (p5 ∧ True)) ∧ p5)) ∧ True) → False)) → p5) ∧ True) ∨ (((p5 ∧ p2) → True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171762810398094067352115065154 : (((((p1 → (((p4 → (True → False)) → p2) ∧ p2)) → (True ∧ p4)) → True) → p4) ∨ (((False ∧ p1) → p3) ∨ ((p4 ∨ (p3 ∧ p5)) ∨ p3))) := by
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
theorem thm_5_vars_49020642237164815303277754918 : (((((((((p3 ∧ p5) → p4) ∧ ((False → False) → (p4 ∨ p5))) ∧ True) ∨ p1) → ((p1 ∨ p1) ∨ False)) → False) ∨ ((True ∨ False) ∨ p3)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667912604194489104380418311431 : ((((p2 ∨ ((((((p1 ∧ p5) → p1) ∧ False) ∨ (((p1 ∧ p1) ∨ p4) ∨ p5)) → p5) → (p1 → (p1 → p4)))) ∧ ((p3 ∧ True) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118491778582016049340517568369 : ((p3 ∨ (((p4 ∨ (((p4 ∨ (((p4 ∧ p5) ∧ False) ∨ p1)) ∨ p4) ∨ p5)) → (p2 → p5)) ∨ ((True ∨ p4) ∨ (p4 → p5)))) ∨ (p2 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_214143558339642138165763599774 : ((((p4 → p5) ∨ True) → p1) ∨ (p1 ∨ ((p2 ∨ ((p5 → ((((p2 → p5) ∨ p5) → p1) ∨ (p4 ∨ (p5 ∨ (True ∨ p3))))) ∨ p5)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_177836516982280089439855134237 : ((((((p1 → p5) → ((p3 ∧ p4) ∨ p1)) ∧ (p5 ∨ False)) ∧ p3) ∨ True) ∨ (False ∧ (p1 ∨ (p2 ∨ (p2 ∨ ((p3 ∨ p2) ∧ (False ∧ p3))))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42267412893118133654755760568 : (((p1 ∧ ((p2 ∨ (((False → p3) ∨ ((p3 ∨ True) → ((True ∨ True) ∨ p4))) → p5)) ∨ ((p5 ∧ p5) ∧ ((p1 → p2) ∧ p1)))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193799659504503734321820733139 : ((p4 ∧ (p5 ∨ (False → ((False ∧ (True ∧ True)) → p5)))) → ((((p1 ∨ ((False ∨ (p5 → p3)) ∨ p4)) ∧ p4) ∨ (p1 ∧ (p2 → p1))) ∨ p5)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115121212473460575724357703828 : (((((False ∨ p5) ∨ (True ∨ (p3 ∧ (True → True)))) → (p4 ∧ p5)) → (False ∨ (((p4 ∧ (p4 ∨ p4)) ∧ p1) ∧ (False ∨ False)))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723946301181353422435836485143 : ((((False ∧ (False ∧ p1)) ∧ ((True → (((p2 ∧ (p1 ∨ p5)) ∧ p3) ∨ (p5 ∧ p2))) ∨ (p1 ∨ (p3 ∧ (p2 ∧ (True ∧ (p3 ∨ p3))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225068969668730373350104309492 : (((p1 ∧ p2) ∧ p2) ∨ ((p1 ∨ ((((p2 → p2) → (p4 ∨ p3)) ∨ (((p1 ∧ (False → p2)) ∧ p1) ∧ p4)) ∨ p3)) ∨ ((p2 → True) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41608660499298521173425888183 : (((((p2 → p3) ∨ ((p5 ∧ (True → p2)) ∨ p3)) ∨ ((((((p2 ∧ p2) → False) ∧ (p5 → True)) ∧ p2) → False) ∨ (False ∧ True))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345669490203766053648143864386 : (p3 → ((p1 ∨ (((((p2 ∨ p5) ∧ (p1 ∨ (p3 → p3))) → False) → ((p3 → (True ∨ p4)) ∧ (((p2 → p2) → False) ∨ p2))) ∧ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311243132302640829329076148498 : (p2 ∨ ((p4 → p4) → ((False ∧ True) ∨ (((p4 ∧ p3) ∨ ((p5 ∨ True) ∧ ((p5 → ((p1 → p5) ∨ p2)) ∨ p1))) ∨ (True → (False → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114944770776612122622130778237 : ((((p4 ∧ p2) ∧ ((p1 ∨ (p5 ∧ (p3 ∨ ((p5 → p4) ∨ False)))) ∧ p1)) → (False ∨ (True ∧ (((p4 → p2) → False) ∨ p2)))) ∨ (p2 ∨ p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h15 =>
        -- False on the left can always be used.
        apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120927283423986097512760016346 : (((((False ∨ (p4 ∧ p2)) → p5) ∨ ((p5 → ((True ∧ False) ∧ p4)) ∧ (True → ((p1 ∧ p5) ∨ ((p2 ∨ p2) → True))))) ∨ p2) → (p5 → p5)) := by
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
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165215476828111622435098218466 : (((((True ∧ (p3 ∧ (p3 ∨ (p5 ∨ p3)))) ∨ p1) ∧ (False → (p5 → False))) ∨ (p3 ∨ p3)) ∨ ((((p1 ∧ p2) ∧ p1) → (p5 ∨ True)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136243724549143343710175840599 : (((p2 ∧ ((True ∧ (p3 ∧ False)) ∧ False)) ∨ (((False → ((False → ((p5 ∧ p4) ∨ p1)) ∧ p3)) ∧ p3) → (p1 → p5))) ∨ ((False ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65071782808688452334025814144 : ((p2 ∨ (p4 ∧ (p5 → (((((p3 ∧ (False ∨ (p3 ∧ False))) ∧ p3) ∧ (False ∨ p5)) → (p3 ∨ (False ∨ True))) → (p1 ∨ (p2 → p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340727439851074579308279075144 : (p2 → (((p5 → (((p1 → (True ∧ (((False ∨ (p4 ∧ (p1 ∨ p5))) ∧ ((p3 ∨ True) ∨ (p4 → p4))) → False))) → p3) ∨ True)) ∧ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54778573134743950178061414389 : (((p1 ∧ (((p1 ∧ p1) ∧ p1) → (p5 ∨ p4))) → ((p2 ∧ (False → (p3 → (False ∨ (p1 ∨ p1))))) ∧ ((True ∨ (p1 → True)) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694747552710999890478208973343 : ((((p4 ∨ ((((p4 ∨ ((p5 → p5) ∨ p5)) ∨ p4) → p5) ∨ (p4 → p1))) ∨ ((p4 ∨ ((p1 ∨ p3) ∧ p4)) ∨ (True ∨ (p5 → p2)))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184259364314298149730729357233 : (((((p3 ∨ p5) → ((p2 → p3) ∧ False)) ∧ (p3 ∨ p4)) → p1) ∨ (((p2 ∧ ((p5 ∧ (False → (p2 ∨ p4))) → p4)) ∧ p4) → (p5 ∨ p2))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350156209639704613865799234566 : (p4 → ((((((p5 ∧ p5) ∨ (False → p4)) ∧ p1) ∧ True) ∧ ((p3 ∧ p2) ∧ (True → ((((p3 → p3) ∨ p3) ∨ False) → (False ∨ p2))))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177942802436749457968634785730 : (((((p2 → p4) ∧ p2) ∨ (((p1 ∧ p4) ∨ p3) ∨ (p4 ∧ p2))) ∨ p5) ∨ ((False ∨ (p1 ∨ p1)) ∨ (((p4 ∧ (p5 → p5)) ∨ True) ∨ p4))) := by
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
theorem thm_5_vars_664159757488771363172253042401 : ((((False ∨ ((((p4 ∧ p2) → ((((True ∨ False) ∨ p5) → p2) ∧ (p1 → (p2 → p1)))) → p4) ∧ (p3 → (p4 ∨ p2)))) → (p1 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640094386034989955834715917288 : ((((((p4 ∨ p2) ∧ False) → (((((p4 ∧ ((False → p5) ∨ p2)) → p3) ∨ p5) → ((p1 ∧ (p3 → p3)) ∧ (p5 ∧ False))) → True)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675429431783773689878741881863 : ((((((p5 ∧ p1) ∧ ((((p3 ∨ True) → p5) ∨ ((p2 ∧ p3) → p5)) → (p5 ∨ (p2 ∨ True)))) → p3) ∧ ((p4 ∨ (p3 ∧ p1)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177795482395018425846957265316 : (((p1 ∨ (False ∧ (p1 ∧ ((((True → p4) ∨ p1) → p2) ∨ p5)))) ∧ p3) ∨ (((False → p1) ∨ (p3 ∨ p2)) ∨ (p4 ∧ (p4 → (p3 → False))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205545598354523010207725647009 : (((p3 ∨ p1) ∧ ((p5 → p1) ∧ p1)) ∨ ((p4 ∨ (p3 → ((p5 → p5) ∨ p5))) ∧ (False → ((((p2 ∧ False) ∨ False) ∨ (p4 ∧ p1)) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68426492914680004259080967335 : ((p3 → ((p3 → False) ∨ (False ∨ (((p2 → p1) → ((False ∨ p3) ∧ p4)) ∨ (True → ((p4 ∧ False) ∨ (p1 ∧ ((p4 → p1) ∨ True)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133907265947074981223982607441 : (((p2 ∨ (((p5 ∨ False) ∧ ((p1 → (p2 ∨ (True → p1))) ∧ p3)) ∨ (p1 ∧ (((p5 ∨ False) ∨ p5) ∨ p2)))) ∧ p1) ∨ ((p4 ∧ p1) → p1)) := by
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
theorem thm_5_vars_201974885065553882385805276230 : (((False → (p3 ∧ (p4 ∨ True))) ∨ True) ∧ (((((False → False) ∨ p5) → (((((p5 → p3) ∨ True) → False) ∨ p2) ∨ p2)) ∧ p3) ∨ (False → p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349065208648274588188561299378 : (p3 → (p5 ∨ ((p2 ∨ p4) ∨ (((p2 ∨ ((p1 ∧ p2) ∨ (True → True))) ∨ (False ∧ True)) ∨ (False ∨ ((((True → p5) ∧ p4) ∨ p4) → p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38137351177426272237191876276 : ((((p2 ∧ (p3 ∧ (((True → (p1 ∧ True)) → (((p4 ∨ p5) → (p1 ∨ p5)) ∨ (p4 ∧ True))) → p4))) ∧ (p2 ∨ (p4 ∧ p2))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722862977378170917929780294722 : (((((p2 ∧ True) ∨ p2) ∧ ((((p1 → p4) ∨ p5) → (p2 ∧ (p3 ∨ (p3 → (p2 → ((p2 ∨ True) ∨ (False ∧ p2))))))) ∨ (False → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233970316719377427522022601412 : ((p5 ∨ (p3 ∧ p2)) → (((True → p5) ∨ ((p4 ∧ ((p5 ∧ (True ∨ (False → p2))) → ((p1 ∨ (p1 ∨ True)) ∧ True))) → False)) ∨ (p5 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721887169638239399539470372577 : ((((p4 ∨ (p5 ∨ (p4 ∧ p4))) → ((((True ∨ False) → (False → (p5 ∨ p4))) ∧ (p5 ∧ p2)) ∨ (False → ((p5 ∨ False) ∧ (p3 → p2))))) ∨ p5) ∧ True) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311927532570764236592350715439 : (p2 ∨ (p3 ∨ ((True ∧ (((((((((p4 ∧ p2) ∧ False) → (p5 ∧ (p4 ∧ False))) → p2) ∧ p3) ∨ p3) → p1) ∨ (p3 ∨ p4)) ∨ p3)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134064393198442487536197231741 : ((((((((((p4 ∨ True) ∨ p2) ∧ (p4 → (p5 ∨ False))) ∧ False) → (p5 ∨ (p5 ∧ p2))) ∧ True) ∨ p2) → p2) ∨ True) ∨ ((p5 ∧ p4) → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50149180127415756135691661565 : (((p1 → (((False → p3) ∧ p1) → ((p1 ∨ ((((p2 ∨ True) ∧ p2) ∧ p5) ∨ p1)) ∧ (p4 ∧ p2)))) ∧ ((p2 → p1) ∧ (False ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692785069821338110940149946805 : ((((((p3 ∧ False) → (False ∧ p5)) → (p3 ∧ ((True ∧ True) ∨ (p2 ∧ p5)))) ∧ (p2 ∨ ((p2 ∧ ((False → p3) → p3)) ∨ (True → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328790884324679590911601742133 : (True → ((((p5 → False) ∧ ((p4 ∨ p2) ∨ p1)) ∨ (True ∧ p4)) ∨ ((True ∧ (True ∨ p5)) ∨ ((True ∨ ((p4 → p5) → p5)) ∧ (p2 → True))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680483146493345026317310158467 : (((((((p2 → (p1 ∨ False)) → True) ∨ (p1 → (p2 ∨ p2))) ∧ (p1 → (p4 ∨ ((False ∧ p2) → False)))) → ((p3 ∧ p5) ∧ (p5 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61627414194461382626718424128 : ((p1 ∧ ((p1 ∧ p1) → (((p3 ∨ ((p4 → ((p2 ∨ p3) ∨ p1)) ∧ ((((False ∧ True) ∨ p1) → p4) ∨ p2))) ∧ (p4 ∧ True)) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172817346221580736587103034519 : ((True ∧ ((p4 ∨ ((p3 → p2) → (p3 ∨ (p2 → p4)))) ∨ ((p3 ∧ p5) ∨ True))) ∨ ((p1 ∨ ((p4 ∧ (p1 ∨ True)) ∧ p1)) ∨ (p4 ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157366282306506192117275290885 : (((p3 → ((((p2 → (p2 ∧ (p5 ∨ (False ∧ p1)))) ∨ (p3 → (False → p1))) ∧ True) → p5)) → p3) ∨ ((True ∨ (True ∧ p5)) ∧ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117793735834449768347448971874 : ((p4 ∧ ((((False ∧ p3) ∨ p5) ∨ (p2 ∧ ((p5 → False) ∧ True))) → (((p5 ∨ (p4 → p5)) → p4) ∨ ((p1 → False) ∧ p2)))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702237700189948972882488678176 : (((((((p5 ∧ False) → (p2 → p4)) → (p1 ∨ p5)) ∧ p2) ∨ ((((True ∨ p1) ∨ (p4 ∨ p3)) → (((p1 ∨ p2) ∧ p3) → False)) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_134518197068516056522025852674 : ((((p4 ∨ (p3 → (((p5 ∨ p4) ∨ (p3 ∧ ((p4 → p3) ∨ ((p1 ∧ p3) → (False → p5))))) ∧ p4))) ∨ p2) → p3) ∨ (p2 → (p2 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62763834991072779687995271323 : ((p4 ∧ ((((((False ∨ p3) ∧ p4) → p2) → (p3 ∧ ((((False → p1) ∧ False) → False) ∨ (False → p5)))) ∨ p5) ∨ ((p1 ∧ p1) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775658613131790252122373127831 : (((False ∨ (p1 ∨ ((p2 ∨ p4) ∧ ((p5 ∨ ((True ∨ p4) ∨ p4)) → (False ∧ (((p4 ∨ False) ∧ ((p5 → False) → (p2 ∨ p3))) ∨ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147116799417875765894642487418 : ((((True ∧ p4) ∨ (p5 → ((p5 → p2) → ((p5 ∧ (p2 ∧ ((p3 ∨ p4) ∨ (p1 → p3)))) ∨ False)))) ∧ False) ∨ (((True ∧ True) ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42006214719329666183991447849 : ((((p3 → False) ∧ ((((p3 ∨ (False → (p2 → (False ∧ p5)))) ∧ (p1 ∨ ((True ∧ (p2 ∨ True)) ∨ True))) ∧ p3) → (p4 ∨ p2))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724676245542829868518624035012 : ((((p2 ∨ (p3 ∨ True)) ∧ ((((False ∨ p1) ∨ p2) ∨ ((p1 ∨ p3) → (False → (((p2 ∧ p4) → p3) ∧ (False ∧ True))))) ∨ (False → p3))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142822025220488929060253712126 : ((p3 ∨ (True ∨ ((((False ∨ p4) → True) ∨ True) ∧ (p2 ∨ ((p1 → (p3 ∧ (p1 ∨ ((p1 ∨ p2) → p5)))) → True))))) → ((False ∨ p5) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
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
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h12 =>
            -- One of the premise coincides with the conclusion.
            exact h4
          case inr h13 =>
            -- One of the premise coincides with the conclusion.
            exact h4
        case inr h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h15 =>
            -- One of the premise coincides with the conclusion.
            exact h4
          case inr h16 =>
            -- One of the premise coincides with the conclusion.
            exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52236899589136062514644898530 : (((p3 ∧ (((p1 ∧ (p2 ∧ True)) ∨ p5) ∨ ((p3 ∨ (False ∨ (p3 ∧ False))) → False))) → (((False ∨ p2) ∧ p1) ∨ ((p1 ∨ False) → p3))) ∨ p2) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h13
  case inr h14 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : (p3 ∨ (False ∨ (p3 ∧ False))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h16 := h14 h15
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58304471522244903273399320631 : (((True ∨ p4) ∧ (((((p5 → ((p2 ∧ (True ∧ ((False ∧ (p1 ∨ p3)) ∨ (False → True)))) ∧ (p1 ∧ p2))) → p5) ∨ True) → p5) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241517984134995389594993601815 : ((False → p3) ∧ (((((p4 ∧ (p2 ∧ p3)) ∨ False) → (True ∧ p1)) → ((p2 ∨ (False ∧ ((p3 ∨ False) ∨ (p1 ∧ (p3 ∧ p1))))) ∨ False)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323650089369681430487209213641 : (p5 ∨ (((p1 → ((p1 ∧ ((True ∧ (False ∨ (p2 ∨ ((False ∨ p3) ∨ True)))) ∨ p2)) ∧ (p2 → True))) ∧ True) ∨ (((p5 ∧ p5) ∧ True) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164761655227058585966354199577 : ((((False ∧ ((p3 → (p5 ∧ True)) ∧ ((p2 ∨ p2) → True))) ∨ ((p4 → p3) → p3)) ∨ p3) ∨ (((p4 → False) → p2) → (p3 → (p1 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116735360485791378767702970385 : (((p3 ∧ p5) ∨ (p5 ∨ ((False ∨ ((p4 ∧ (False → p1)) → ((True ∧ (p1 ∨ p2)) ∨ (True ∨ (False ∧ (p1 → p4)))))) ∨ p3))) ∨ (p4 ∨ p2)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227352698576707280763479436362 : (((p3 → p2) → p3) ∨ (((p2 → ((p3 ∨ (p5 → ((((p1 ∧ (True ∨ False)) ∨ p3) ∧ p2) ∨ (p1 → p5)))) ∨ p3)) ∨ p3) ∨ (p4 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352825457254706844865088690982 : (p4 → ((False → p1) → (((False ∧ p1) ∨ ((p3 ∧ (p3 ∨ ((p3 → p5) ∨ (p5 → (True ∧ True))))) ∧ True)) ∨ (((True ∨ p4) → p4) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59173644505349136002087406590 : (((False ∨ p4) ∨ ((p4 ∨ p4) ∨ ((p1 ∨ (False → False)) → (((False ∨ True) ∧ (True ∧ p2)) → ((p1 ∧ (p5 ∨ p4)) ∨ (p4 → True)))))) ∨ p2) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h4.left
    let h8 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347033661526783507565887782596 : (p3 → ((((p1 → False) ∧ ((False ∧ True) ∨ (((False → (False → p3)) ∧ p5) → p4))) ∧ p1) → ((((p1 ∨ (True → p3)) → False) ∧ p2) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h12 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h13 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h14 := h7 h13
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h2.left
    let h17 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- False on the left can always be used.
      apply False.elim h21
    case inr h23 =>
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h24 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h25 := h18 h24
      -- False on the left can always be used.
      apply False.elim h25
  -- Conjunctions on the left can always be decomposed.
  let h26 := h2.left
  let h27 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h28 := h26.left
  let h29 := h26.right
  -- Disjunctions on the left can always be decomposed.
  cases h29
  case inl h30 =>
    -- Conjunctions on the left can always be decomposed.
    let h31 := h30.left
    let h32 := h30.right
    -- False on the left can always be used.
    apply False.elim h31
  case inr h33 =>
    -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
    have h34 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h27
    -- We have shown the premise of h28, we can now drive its conclusion.
    let h35 := h28 h34
    -- False on the left can always be used.
    apply False.elim h35
  -- Conjunctions on the left can always be decomposed.
  let h36 := h2.left
  let h37 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h38 := h36.left
  let h39 := h36.right
  -- Disjunctions on the left can always be decomposed.
  cases h39
  case inl h40 =>
    -- Conjunctions on the left can always be decomposed.
    let h41 := h40.left
    let h42 := h40.right
    -- False on the left can always be used.
    apply False.elim h41
  case inr h43 =>
    -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
    have h44 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h37
    -- We have shown the premise of h38, we can now drive its conclusion.
    let h45 := h38 h44
    -- False on the left can always be used.
    apply False.elim h45



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136703045745941485260555796872 : (((p1 ∧ p1) ∧ ((p3 ∨ ((p2 ∧ (p3 ∧ ((p2 → p5) ∧ True))) ∨ (False ∨ p2))) ∨ ((True ∨ (p3 ∧ p4)) ∧ True))) ∨ (True ∨ (False ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263969293491931935596865675198 : (True ∧ (((((((p2 → False) ∧ False) ∧ p4) → (p4 ∧ p5)) → p2) ∧ True) ∨ (p3 ∨ (((p1 ∧ ((p3 → False) ∨ p2)) → (True → True)) → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46961415494791147458317126836 : (((((((p4 → ((p4 → p5) → (((p3 ∧ p1) ∧ (False ∧ (p4 ∨ p1))) ∧ (p1 → True)))) ∧ p1) ∧ p2) ∨ p3) → False) ∨ (p1 → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



