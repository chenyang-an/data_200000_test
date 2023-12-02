variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218296414327993580975478191570 : (((p4 ∨ p1) ∨ (p5 → p1)) → ((p4 ∨ (((True → (p1 ∨ ((False → (p4 ∧ p4)) ∨ p4))) ∧ p4) ∨ (p2 ∨ True))) ∨ (p5 → (False ∧ p5)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
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
  case inr h5 =>
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
theorem thm_5_vars_653179761086215913084630474750 : ((((p1 → (((((False → (True ∧ False)) → (p4 ∨ p3)) ∨ False) ∧ (((False ∨ (p1 → (False → False))) ∨ p4) ∧ p3)) ∧ p5)) ∧ (False ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177631432383360049407011388633 : ((((((p4 ∨ ((p3 ∧ p5) ∧ False)) ∨ p4) ∧ (p3 ∨ p3)) ∧ p3) ∧ p4) ∨ (False ∨ ((((True ∨ ((p3 ∨ p4) ∨ p1)) ∨ False) ∨ p3) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624776833433837297525029924619 : ((((p5 ∨ (((((True ∧ ((p5 → p4) ∨ False)) → (((False ∨ True) ∧ False) ∧ True)) ∨ (p5 ∨ True)) ∨ (p1 ∨ (p3 ∨ True))) ∨ p2)) ∨ p4) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232083638128994631296518882362 : (((p4 ∨ p3) → p5) → ((p2 ∧ p5) ∨ (((((False ∧ p5) → p5) ∧ (p5 → True)) ∧ (False ∨ p5)) ∨ (p4 → ((p2 → (False ∨ p5)) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (p4 ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319722966164774555667660937113 : (p4 ∨ ((p4 ∨ ((p5 ∨ False) ∨ (False → p3))) ∧ (((False ∧ p1) ∧ p4) ∨ (((True ∧ True) ∧ (p1 ∧ p1)) ∨ ((p2 ∨ False) → (False ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717256960785456799286006040942 : ((((p3 ∨ (p4 ∧ (p4 ∨ p3))) ∧ (((p5 ∧ False) ∧ p3) ∨ ((True ∨ p3) ∧ (((p3 ∨ (p2 ∨ (True ∨ False))) → p5) ∧ (True ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48688350991346627079821506925 : ((((p3 → ((p1 ∨ ((True ∨ p4) ∧ p5)) ∧ True)) ∧ ((True ∨ ((p4 ∨ (p1 → p1)) ∨ p4)) ∧ (p1 ∧ p2))) ∧ ((p3 → p1) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322411212490080651603911951671 : (p5 ∨ (((p4 ∧ (p5 ∧ (((p2 ∧ p4) → p4) → (p1 ∧ p2)))) ∧ (False ∨ (p1 ∧ (True ∧ (p4 ∨ ((p2 ∨ (p4 ∧ False)) ∧ p5)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166124441562563959820477521308 : ((True ∧ (((p5 ∨ (p4 ∧ ((p1 ∨ (p2 → (p2 → p5))) ∨ False))) → p2) ∨ (True → True))) ∨ ((p1 ∨ (p5 → (False ∨ (p2 ∧ p1)))) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159751793775939529765115560672 : (((((True → False) ∨ p5) ∧ (((p1 ∧ (((p5 ∨ False) ∧ (p5 ∨ p2)) ∧ p4)) → True) ∧ p1)) ∨ p5) → (p5 ∨ (p5 ∧ (p5 → (True → p3))))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h4.left
      let h7 := h4.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h9 := h5 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h4.left
      let h12 := h4.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h13 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40445030966632061364493643969 : (((((((p3 ∧ p1) ∨ (p4 ∨ p2)) ∧ p4) ∧ (((True ∧ True) ∨ p2) ∧ (p2 ∨ ((p5 → ((p3 → p4) ∧ p2)) ∧ False)))) ∨ p2) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178398478604849177380642167320 : (((((True → p4) ∨ p2) ∨ ((p4 ∧ p3) ∧ (False → True))) → (p5 ∧ p1)) ∨ (p4 → (((True ∨ p2) ∧ True) ∨ (False ∨ (True ∧ (False ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67327960125081881746670363479 : ((p1 → (((p3 ∨ ((True ∨ False) ∧ (True → (p1 → (((p4 → (((p1 ∧ p4) → True) → p2)) ∨ p4) → (p4 ∧ p5)))))) ∨ p1) ∨ p4)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_26511211948220039464747710555 : (((False ∧ False) ∨ (((((True → True) ∨ p3) ∧ (p4 → (p3 ∧ (p3 → (p5 ∨ p2))))) ∨ ((p5 ∧ (p3 ∨ (p2 → True))) → True)) ∨ p2)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177844795024386447362231964305 : ((((p2 ∧ (((False ∨ p4) ∨ p5) ∨ (p5 ∨ (True ∨ p4)))) ∧ False) ∨ False) ∨ (((True ∨ p3) ∧ (((p1 → False) → False) ∧ (p5 ∧ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120043948638582907203757735196 : (((((p3 ∨ p5) → (True ∨ ((p1 ∨ (True ∧ p5)) → p1))) → (((p1 ∨ (p1 ∨ ((False ∨ p1) ∧ False))) ∧ p1) ∨ p1)) ∧ p3) → (False ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p3 ∨ p5) → (True ∨ ((p1 ∨ (True ∧ p5)) → p1))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h4
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h18 =>
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- False on the left can always be used.
          apply False.elim h17
  case inr h20 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38627302618529055393626794081 : (((((False → (False ∨ (p3 → p2))) ∧ (p4 ∨ p2)) ∨ (((True ∨ p3) ∧ p2) → ((p4 ∨ p3) ∧ ((p1 ∧ (False ∨ p4)) → p4)))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775460198413128946832731935150 : (((False ∨ (p3 ∧ (((p2 ∧ p1) ∨ p3) ∨ (True → ((False ∨ ((p1 ∨ False) ∧ ((p2 ∧ ((True ∨ (p2 ∨ p5)) ∧ False)) → p2))) ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217590876397965383685668573620 : ((((p5 ∨ False) ∨ p3) → True) → (((p1 ∨ p2) ∨ ((((False ∨ (p4 ∨ p5)) ∨ ((p1 → p3) ∨ p5)) ∧ (p1 ∨ (p3 → p3))) → p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134829147155695840315931279511 : (((p1 ∨ (p1 ∨ (((((True ∨ p2) ∧ True) ∧ True) ∨ (p1 ∨ (p3 ∨ p4))) ∨ (p2 ∧ (p3 ∨ (p3 ∨ p2)))))) → False) ∨ ((p1 → p1) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208344539299896560350728991247 : (((p4 → p3) ∧ ((p4 → p3) ∨ p3)) → ((((p3 ∧ False) ∨ p3) ∨ (((p4 ∧ p3) ∧ ((p5 ∧ p3) → ((p4 → True) ∨ p5))) ∨ True)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233322953322440790031726897870 : ((True ∨ (False → p1)) → (((((p4 ∨ (False ∨ p2)) ∨ ((False → True) ∨ (p4 ∨ p2))) ∧ p3) ∨ p5) ∨ ((((False ∧ False) ∧ p3) ∧ p5) → True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187483716655908053013874346569 : ((False ∨ ((False ∨ ((p5 ∨ True) → (p5 → p4))) ∧ (p5 ∧ p4))) → ((p3 → p3) → (True ∧ (False ∨ ((p4 → (p1 ∨ p2)) ∨ (True ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h6.left
      let h10 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339823752860986871674955251349 : (p1 → (p5 ∨ (p1 ∧ (p2 ∨ ((p2 ∧ (p4 → (True → p5))) ∨ (((((p1 → p3) ∨ (p2 ∨ False)) ∨ p4) ∨ p2) ∨ (True ∧ (True → p1)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309339200734351824221359576743 : (p2 ∨ (((True ∧ (p1 ∧ ((((((((p2 → p2) ∧ p1) ∨ False) → p4) → p2) ∧ p2) ∨ False) ∨ p5))) ∧ (False → (p5 ∧ p2))) ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149974764699824927540665218699 : ((p4 ∨ ((((p4 → (p2 ∧ (p5 → p2))) → True) ∧ p1) ∧ (((p4 ∧ (p3 ∨ (p4 ∨ p3))) ∧ p3) ∧ p3))) ∨ (((p5 ∨ False) ∨ p5) → p5)) := by
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
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53709917809318177718785329282 : (((p2 ∨ ((p2 ∧ ((p4 ∨ True) → p5)) ∧ (False ∧ p4))) ∧ (((p1 ∨ p4) ∧ (p3 ∨ False)) → (p5 → ((False ∧ (p1 ∧ p1)) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49814444195638623822287658370 : (((p1 → ((p2 → (p1 ∧ p5)) → ((p1 ∨ p1) ∨ ((p2 ∨ p1) ∧ (((p2 ∧ (p1 ∧ True)) → p2) → True))))) → (p1 ∧ (False → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59190005257311640458654423880 : (((p1 ∨ False) ∨ ((True ∨ (p5 ∧ (p3 ∨ False))) → (p3 ∧ (False ∧ (((p3 ∧ p4) ∨ ((p3 → p2) ∧ (p2 → p5))) ∧ (p4 ∨ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149389224421889459873927151208 : (((p5 → p2) → (((True → p1) ∨ ((p2 ∨ True) ∧ p3)) ∨ ((p2 ∧ p5) ∧ (p2 ∨ ((p3 ∧ p3) ∧ p1))))) ∨ (p5 → (p1 → (p1 ∨ p5)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230386125372519293664369817333 : (((p3 ∨ p3) ∧ True) → ((((p3 → (p1 → p1)) → (p5 ∧ (p2 → p2))) ∨ p4) → (((True → (p3 ∧ p2)) → (p2 ∨ False)) ∧ (False → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h9 := h3 h8
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h13 := h3 h12
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h1.left
    let h17 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h18 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h19 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h20 := h3 h19
      -- We need to get the right conjuct of h20 based on <expert-advice>.
      let h21 := h20.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h22 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h23 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h24 := h3 h23
      -- We need to get the right conjuct of h24 based on <expert-advice>.
      let h25 := h24.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h25
  -- Implications on the right can always be decomposed.
  intro h26
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171380114842204447113393519865 : (((((True → ((p1 ∧ p5) ∨ (p3 ∨ p1))) → p3) ∨ (p1 → (False ∧ True))) ∧ p3) ∨ (p4 ∨ ((p1 ∧ ((p2 → True) ∨ True)) → (True ∧ True)))) := by
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
theorem thm_5_vars_85141330379697773266568291461 : ((((((p5 ∨ p2) → (p4 → (p4 ∨ (p3 ∨ p4)))) ∨ False) ∨ (p5 ∨ p1)) → (((p4 ∧ (p2 ∧ (False → p5))) ∧ (False ∨ p5)) ∧ p1)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p5 ∨ p2) → (p4 → (p4 ∨ (p3 ∨ p4)))) ∨ False) ∨ (p5 ∨ p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148013453147284564927791519141 : ((((p5 ∨ ((p2 ∨ False) ∨ ((((p2 → p5) → p2) ∧ p5) → p3))) ∨ (p4 ∧ (p1 → p4))) ∨ (p1 → p5)) ∨ (p5 ∨ (p3 → (p1 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48210612760949656640426090938 : ((((p2 ∨ p2) → (((((((p5 ∧ (p3 ∨ True)) ∨ (p3 ∨ p2)) ∨ True) → p5) → p3) → False) ∧ ((p3 ∧ True) ∧ False))) → (p5 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156602805928888325460095714320 : (((((p4 ∨ ((p3 ∧ ((False ∧ False) ∨ p4)) ∨ p4)) ∧ ((p3 ∨ (p4 ∧ True)) ∨ p5)) ∧ p2) ∧ True) ∨ (p1 → ((True ∨ p3) ∨ (p3 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728172084647991382449077128871 : ((((p5 ∨ (p2 → p3)) ∨ (((((p2 → (False ∨ p5)) ∧ (p4 ∧ p1)) ∨ (p3 → p3)) ∧ (((p1 ∨ True) ∧ p2) ∨ True)) ∧ (True ∧ True))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197828444764646573291476639579 : (((p2 ∧ (p1 ∨ p3)) ∨ (p3 ∧ (p3 ∨ p5))) ∨ ((p4 → ((False → (p4 ∨ p5)) ∨ ((p3 → (p1 ∨ p2)) ∨ p2))) ∧ (False → (p4 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184050634047199327587283125914 : ((((p1 ∨ (((p3 ∧ False) → p4) ∧ True)) ∧ (p2 → p5)) ∨ False) ∨ (((p2 ∨ ((p5 ∧ False) → ((p4 → p5) → p5))) → False) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134045917323648395984789420997 : (((((p4 ∨ p1) ∨ ((False ∧ p3) ∧ (p3 ∨ (p1 → (p1 ∨ (p4 ∨ ((False → (p3 → p2)) → p3))))))) ∨ p5) ∨ True) ∨ ((p4 ∨ p4) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354762641499405314600504195326 : (p5 → ((((p1 → ((p1 ∨ (p3 → False)) ∨ p1)) → ((p2 → False) → p1)) ∧ ((True ∨ p3) → ((p3 ∧ p4) → (p4 → (p4 ∨ p2))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177896647532019335392964768074 : (((((p5 ∧ p4) → ((p2 → p1) ∨ (p4 → p5))) ∧ (p5 ∨ p4)) ∨ False) ∨ (((True → ((p2 → False) ∨ p4)) → ((p1 ∧ True) → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676228969254257152432978739950 : ((((((True ∨ p1) ∧ p5) ∨ (p3 → ((p2 ∧ (((p3 ∨ p4) ∧ p1) ∨ False)) ∨ ((p4 → p4) ∨ True)))) ∧ (False ∨ ((p2 → True) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316875670289341791459282250445 : (p3 ∨ (p1 → ((p4 ∧ (p5 ∧ (((p5 → p1) ∧ (p3 ∧ p3)) ∧ p5))) ∨ (((p2 → p5) ∧ p1) ∨ ((False ∨ (p4 ∨ p5)) → (True → p1)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217283503495435859645440301038 : (((p3 ∧ (p2 ∨ p5)) ∨ p1) → (((((p1 ∨ (True → True)) → ((p2 ∨ p3) → p1)) ∧ (p1 ∧ True)) ∨ p1) ∨ (False ∨ (True ∧ (p4 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
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
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205321015574532812765497307838 : (((p5 ∨ (p2 ∨ p4)) ∨ (p3 ∨ False)) ∨ (((((p5 ∧ p2) → p4) ∨ p3) ∧ False) ∨ (((p1 → ((p5 → p2) ∧ (p3 ∧ False))) → True) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165181453561372514283097688517 : (((p5 ∨ ((p2 ∧ (((True ∨ ((p3 ∧ p5) ∨ p3)) ∧ True) ∧ True)) ∧ True)) ∧ (p3 → p2)) ∨ ((p3 → ((p1 ∧ p5) ∨ p3)) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171817503599481836822730266556 : ((((((p5 → p1) ∨ p1) ∧ p2) ∧ (p1 ∨ (p3 ∨ ((p5 → p2) → p4)))) → False) ∨ ((((p4 ∨ (True ∧ p2)) → (p1 ∨ False)) ∨ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265755046136222385573067478196 : (True ∧ (p4 ∨ ((((((False ∧ p1) → p5) ∧ ((True ∨ p5) → False)) ∧ (((True ∧ p3) ∨ True) ∨ (((p4 → p4) ∧ p1) ∨ p3))) → p3) ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h11 : (True ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h12 := h5 h11
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h17 : (True ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h18 := h5 h17
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352103161853167384437333159635 : (p4 → ((((False ∨ p1) ∧ p4) ∧ (False → False)) ∨ ((False ∨ (((p1 ∧ False) ∧ (True → p2)) ∨ p2)) ∨ ((True ∧ True) ∨ (False → (False ∧ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_799075462652077306782454209597 : (((p1 → ((p3 → p2) → ((p2 → ((p2 → ((p4 ∨ p1) ∧ False)) ∨ False)) → (p1 → (p3 → ((((True ∧ True) ∧ p4) ∧ p2) ∨ False)))))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : p2 := by
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h6
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : p2 := by
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h12 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h13 := h2 h12
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h14 := h10 h11
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- False on the left can always be used.
    apply False.elim h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52660860825411139312027098206 : (((p3 ∧ (False ∨ (p2 → ((True ∧ p2) → ((False ∨ False) ∨ (p5 ∨ p3)))))) ∨ (((False → ((p2 ∨ p4) ∨ (p3 ∧ p5))) ∧ False) → True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207347219699857475816018044793 : ((((p3 → True) ∨ (p2 → p1)) ∨ p2) → ((((p4 ∧ ((False ∧ (True → ((p5 ∨ p4) → p1))) ∧ (p1 ∧ True))) → p4) → p2) ∨ (p4 → True))) := by
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
theorem thm_5_vars_354744853652506001493307338465 : (p5 → (((((p1 ∧ (((p2 ∨ p4) ∧ (p5 ∧ p3)) ∧ ((p2 ∧ False) ∧ p3))) ∧ p3) ∨ p5) ∨ (p4 ∧ (False → (p5 → (True ∧ p1))))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225803768179133231122051446318 : (((True ∧ False) ∨ False) ∨ (((False ∧ (p3 ∨ (p1 ∧ (((((p3 ∧ p5) → True) ∧ ((p3 ∧ (p3 ∨ p4)) → p5)) ∧ p3) → False)))) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129357411725702615835252074828 : (((False ∧ (p1 → (((p1 ∨ (p5 ∧ ((p1 ∨ True) ∧ p1))) → (p1 ∧ (p5 → (p5 ∧ False)))) → (p2 ∨ p3)))) ∨ True) ∧ (True ∨ (False ∧ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161641437490160510210683299413 : ((p1 ∨ (((((p1 ∨ p2) → (p3 → (p3 ∨ p5))) ∧ (((p5 → p3) ∨ p2) ∨ p2)) ∨ p2) ∨ p5)) → (p5 ∨ (((p5 ∧ p3) ∧ p2) ∨ True))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h9 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h10 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160679427973058768901817496025 : ((((p5 ∧ ((False ∨ True) ∧ (False ∨ p1))) → p4) ∧ (True ∧ ((p5 ∨ (p2 ∨ p1)) ∨ (False ∨ False)))) → (((p3 → True) → (False ∧ p1)) → p1)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h9 : (p3 → True) := by
        -- Implications on the right can always be decomposed.
        intro h10
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h9
      -- We need to get the left conjuct of h11 based on <expert-advice>.
      let h12 := h11.left
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h15 : (p3 → True) := by
          -- Implications on the right can always be decomposed.
          intro h16
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h17 := h2 h15
        -- We need to get the left conjuct of h17 based on <expert-advice>.
        let h18 := h17.left
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- One of the premise coincides with the conclusion.
        exact h19
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- False on the left can always be used.
      apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190623267616089002004406877277 : (((p2 ∧ (((p1 ∨ (False ∧ True)) ∧ p5) → True)) → p5) ∨ (p3 ∨ ((True ∧ (((p4 → p4) → p3) ∧ ((p1 ∨ p4) ∨ p3))) ∨ (False ∨ True)))) := by
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
theorem thm_5_vars_43093667197613030519909727458 : ((((((True ∨ (True ∨ p1)) → (p3 ∨ (((False ∨ (True ∧ p5)) ∧ (p2 ∧ (p2 ∨ (p4 ∧ True)))) ∨ p4))) → (p1 ∧ p3)) ∧ p5) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178489945997494395054470189759 : ((((p4 → (p1 ∨ p2)) → ((p4 → p1) → p3)) ∨ ((p5 → p5) ∧ p2)) ∨ ((((((True → p1) ∧ p3) ∧ p3) ∨ True) ∧ (False ∨ p3)) → p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228070465486862230185626531750 : ((p4 ∧ (p4 ∧ False)) ∨ (False ∨ ((p5 ∨ (((p3 → (False ∨ (p5 ∨ (True → (p1 ∧ p3))))) ∨ True) ∧ (p1 → (p5 ∧ p1)))) ∨ (True ∨ p2)))) := by
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
theorem thm_5_vars_213088351085537369212115404978 : ((((p4 ∧ p3) ∧ p2) ∧ False) ∨ (p4 ∨ ((p3 → ((p5 → p5) ∨ ((False → ((True ∧ ((p1 → p5) ∧ True)) ∧ p2)) ∨ True))) ∨ (p4 → p1)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638741298538779576077056727944 : (((((False ∧ ((p2 → False) → (p2 ∨ True))) → (p1 ∧ (True → ((p1 ∨ ((p1 ∧ p1) ∧ ((p3 ∨ p5) ∧ p3))) ∧ (p1 ∨ p4))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55204764793367215458915497868 : (((((True ∧ p4) → True) ∧ (p2 ∨ p2)) ∨ ((((True ∧ (p2 ∨ (p5 ∧ False))) ∧ (False → (True → p2))) ∨ (True ∧ p1)) ∧ (p2 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183472812717888893568982841914 : ((p3 ∨ (((p2 ∨ True) ∧ (p3 → (True ∨ (p1 ∨ p4)))) ∨ False)) ∧ ((p3 ∨ p1) → ((p2 ∧ (p1 ∨ ((True ∧ p3) ∨ (False ∧ p4)))) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113092016805442375572876100662 : (((p5 ∨ ((((((((p4 ∨ p4) ∧ p1) ∧ (True ∧ False)) → p5) ∧ p1) ∧ p2) → p5) ∧ (p4 ∧ ((p2 → p2) ∧ True)))) → False) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194980108138972395495477548423 : ((((p3 → p1) → (p5 ∧ (p2 ∨ p1))) → True) ∧ ((p1 ∧ (p4 ∧ True)) → ((False → True) → ((True ∧ ((p1 → p2) ∧ (p1 ∨ p1))) ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149186044950874593492130645541 : (((p1 → p4) ∧ (p4 ∨ ((False → (p3 ∧ (True ∧ ((p2 → (p1 → True)) → p4)))) ∧ ((p1 ∨ p3) ∧ p5)))) ∨ ((p1 ∨ (p5 ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745459970726322875337701518523 : ((((p5 ∧ p5) → (p1 ∨ ((False ∨ (p5 → False)) ∨ ((((True → ((p2 → p2) ∧ False)) → (False ∧ p4)) ∨ (p5 → p2)) ∨ (True ∧ p1))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117313801623747754497535481492 : ((False ∧ ((p2 ∧ ((p4 → (((True → p4) → False) → ((False → False) ∨ p5))) ∧ False)) ∧ (p1 ∧ (((p4 ∨ True) ∧ True) ∧ p3)))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356772233915461062549315689292 : (p5 → (((p4 → p2) ∨ ((p1 ∨ True) ∧ p5)) → ((False ∨ ((False ∧ (True ∨ (p4 ∨ True))) ∨ ((False → p4) ∨ p2))) ∨ (p2 ∨ (p1 ∨ p4))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62142590889244416039065618706 : ((p2 ∧ (True → ((False → (((((p1 → p5) ∧ (((p2 ∧ True) → (p5 → (p2 ∧ False))) ∨ (p4 ∧ p4))) ∧ p4) ∧ p4) ∨ False)) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84753107948583987992027606853 : ((((((p2 ∧ (p5 ∧ p3)) ∧ p1) → True) → ((p2 ∨ (p5 ∧ p4)) ∧ False)) ∧ ((((p2 ∨ (p4 ∨ True)) ∨ p4) ∨ (p2 ∨ False)) → True)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p2 ∧ (p5 ∧ p3)) ∧ p1) → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111769110883148791197317547544 : (((((False ∨ p3) → (((p4 ∨ p1) ∨ (((True ∨ (False ∧ p1)) ∨ (p1 → (True ∨ p2))) ∨ p4)) ∧ p5)) ∧ (p1 ∧ p2)) ∨ p4) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617516037554161541967488277093 : ((((((p4 ∧ (p2 ∨ p1)) ∨ (True ∨ p1)) ∧ ((p5 ∧ (True ∧ ((p1 ∧ ((p2 → p2) → p2)) ∨ False))) ∨ ((p1 ∧ p2) ∨ p5))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57381007816527768739472706714 : (((p5 ∧ (p2 → False)) ∨ ((p3 ∨ (((p3 ∧ (p3 → p1)) → (p4 ∨ (p3 ∨ False))) ∧ (False ∨ p4))) ∨ (p4 ∨ (True ∨ (p3 ∧ p4))))) ∨ p1) := by
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
theorem thm_5_vars_623815182510931547643710053319 : ((((p1 ∨ ((False → (p4 → False)) → ((((((p2 ∧ (False → (p2 → (p1 ∨ p3)))) ∨ (p5 → True)) ∧ p5) ∨ p3) ∧ p5) ∧ p3))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_173152664177585915840371555845 : ((p3 ∨ ((True → (p5 ∨ False)) → (((p2 ∧ False) ∨ ((p3 ∨ p2) ∨ False)) ∨ p5))) ∨ (p3 → ((True ∨ p2) ∨ (p1 ∨ ((p4 ∧ p2) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241397082007895531103286415692 : ((False → p1) ∧ ((((p2 → p2) ∨ p1) → (((p2 → p2) → p1) ∨ ((p1 ∧ p2) ∨ ((((p3 → p5) ∧ (True ∨ False)) ∧ False) → p3)))) ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321340911903094532654291185053 : (p4 ∨ (p5 ∨ (True → (((((((p3 → p2) → p5) ∨ p4) ∨ p1) → False) → p4) ∨ ((p3 ∧ p2) ∨ (p1 → ((p1 ∧ (False ∨ p2)) → p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208572411276578660398104757376 : (((True → False) → ((p5 ∧ True) → p3)) → ((p4 ∧ (True ∧ p5)) → (((p5 ∧ ((p1 ∧ False) ∧ p5)) ∨ (p2 → True)) → (p3 ∨ (True ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h2.left
    let h13 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67413822258702284332561331171 : ((p1 → (((p5 ∨ (((((p4 ∧ ((((p4 ∨ p1) ∨ p5) ∧ (p1 ∧ p3)) ∧ p1)) ∧ True) ∨ True) → True) ∧ True)) → False) ∨ (p5 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307265348163225882025875976732 : (p1 ∨ (p2 ∨ (((((p1 ∧ ((False → True) → p1)) ∨ p5) ∨ p5) ∨ True) → (p3 ∨ (((p4 ∧ ((p4 ∧ False) ∧ (p4 ∨ p5))) ∧ True) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Conjunctions on the left can always be decomposed.
        let h5 := h4.left
        let h6 := h4.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347497433686372169542561306155 : (p3 → ((p2 ∨ (False ∧ (p1 ∨ (True ∧ p2)))) ∨ (((p2 ∧ p3) ∨ True) → (p4 ∨ (((p2 ∨ p5) ∨ p5) → ((p3 ∨ p2) → (False → p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356563792115672698023651177875 : (p5 → ((((True ∨ p5) ∧ True) ∨ ((p2 ∧ p3) → (p5 ∨ p3))) → (p5 → ((p3 → ((p1 → False) → (p4 ∧ p1))) ∨ ((p4 → p5) → True))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
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
theorem thm_5_vars_351824125635746227756233814252 : (p4 → (((p5 ∧ p5) ∧ ((p2 ∧ (True ∧ (p4 ∨ p1))) ∧ (p1 ∨ p5))) ∨ (True ∨ (p1 ∧ ((False ∧ p3) → ((p3 → (True ∧ p3)) ∧ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962448113849589137263943735327 : ((((True → p1) ∧ (((p5 ∨ p4) ∧ ((p2 → (False ∧ (p5 → (p3 ∧ False)))) → (p1 ∧ p1))) ∨ ((p5 ∧ p5) ∨ ((p2 ∨ p4) ∨ p1)))) → p1) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h9 := h2 h8
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h11
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h18 := h2 h17
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h22 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h23 := h2 h22
          -- One of the premise coincides with the conclusion.
          exact h23
        case inr h24 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h25 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h26 := h2 h25
          -- One of the premise coincides with the conclusion.
          exact h26
      case inr h27 =>
        -- One of the premise coincides with the conclusion.
        exact h27
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206171631965188625553188309737 : ((p5 ∧ ((p4 ∨ p4) ∨ (p4 ∨ p3))) ∨ (True ∨ (False ∧ ((((False ∨ False) ∧ (p2 → p3)) ∧ (True ∧ (p3 → ((p4 ∨ p2) ∨ p4)))) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112783038737968929557917968806 : (((((p2 ∨ False) → (False → ((p1 → p3) → p2))) ∨ ((p4 ∨ p1) → ((False → (p3 ∧ p1)) → (True ∨ (p1 ∧ p3))))) → p3) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351653173368503738513433408859 : (p4 → ((p2 → ((p2 ∧ p1) ∨ (False ∧ ((p4 → True) → (p1 ∧ ((p5 → False) ∧ p4)))))) ∨ ((False ∨ (p3 ∧ (False ∨ p3))) → (True → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593357328122172479300271982649 : ((((((True → ((p1 ∧ p4) ∧ (((p2 ∧ (p2 → p1)) ∧ p1) ∧ ((False → (p2 ∧ p1)) ∨ p5)))) ∨ p2) → (p4 ∧ (False ∧ p4))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655415413955615847701569065356 : ((((((((p4 ∨ p1) → (p3 ∧ p3)) → p5) ∨ (((False ∨ p2) → (p4 ∧ (p2 ∧ (p3 → p3)))) → p3)) ∨ (False → True)) ∨ (p5 ∧ p5)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_341710028596874690703459347407 : (p2 → (((((((p1 → p5) ∨ p2) ∨ p3) ∨ p4) → (True → ((p3 → False) ∨ p5))) ∨ ((p4 → p2) ∧ ((False → p5) ∧ p2))) ∨ (True ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148497419945797557037553792645 : ((((p2 ∧ p4) ∧ ((p1 ∧ p5) → (((p1 ∨ False) → True) → p4))) ∨ (((p2 ∧ False) ∧ p2) → (p2 ∨ False))) ∨ (True ∨ (p5 → (False ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225939145311970431815820467391 : (((p2 ∧ p3) ∨ False) ∨ ((p1 ∧ (True → p5)) → (p4 → (p2 ∨ ((False ∨ (((p1 ∨ False) → p2) → p1)) ∨ ((p3 ∧ p4) → (p5 ∨ p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307666973104157408038232651541 : (p1 ∨ (p2 → (((p1 ∧ (p2 ∧ ((True ∨ ((p3 → (p1 ∧ (p3 ∨ p5))) ∨ p2)) → ((p3 ∨ p3) → False)))) ∨ ((False ∧ p2) ∨ p3)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249600631389712858101532641331 : ((p5 ∨ p3) ∨ (((True → ((p4 → (p3 ∨ True)) ∧ (p5 ∧ p4))) ∨ (p5 ∧ ((p4 ∧ (True ∧ ((p2 ∧ p5) → p4))) ∧ (p4 → p5)))) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- We need to get the right conjuct of h4 based on <expert-advice>.
    let h5 := h4.right
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50219725737263536911844175998 : (((((p1 ∨ False) ∧ ((p1 ∧ (True ∨ (p3 → (p1 ∧ p4)))) ∨ (False ∨ (False → (p1 ∧ p1))))) ∨ p5) ∨ ((True ∨ p1) ∨ (True ∧ p5))) ∨ p5) := by
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



