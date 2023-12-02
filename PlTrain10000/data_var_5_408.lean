variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111924522643285078342042329013 : ((((p4 ∧ (((p4 ∧ (p3 → (True ∧ True))) ∧ True) → (p1 ∨ True))) → (True → (((p1 ∧ p1) ∨ (p3 ∨ False)) ∨ p3))) ∨ True) ∨ (p2 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316569899927317252801428299158 : (p3 ∨ (p3 ∨ ((p1 ∨ (((((p1 ∧ (False ∧ p4)) ∨ p5) ∧ (p4 → True)) → p2) ∧ p3)) → (p2 → (p5 → (((p3 ∨ False) ∨ p2) → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h7 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208393566495813275629938838183 : (((p5 ∧ p2) ∨ ((p2 ∨ False) → p2)) → (((p1 ∨ (p3 → p1)) ∨ (p5 ∨ (p3 → (False ∨ (True ∧ ((p4 ∨ p4) ∨ True)))))) → (p4 ∨ True))) := by
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
      cases h1
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
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
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h10 =>
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
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774197646024216567689382410382 : (((False ∨ (((((p3 ∧ (p1 → p5)) → (p2 ∨ ((p5 ∨ p3) ∧ True))) ∨ ((p4 → p1) ∧ (p4 ∨ p1))) → p1) ∧ ((p5 ∨ p3) → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205110785329944192523647068743 : ((((p5 ∧ True) ∨ p1) ∧ (p5 ∨ p5)) ∨ ((p4 ∨ (((p3 → (p2 → ((True ∧ (p5 ∨ p3)) → (p1 → p3)))) ∨ p2) ∧ (False → p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56531450133638255800737839784 : (((False ∨ ((p3 → p3) ∧ p5)) → (True ∧ ((p5 ∧ (p4 ∧ ((((False ∧ p1) ∨ p1) → p3) → True))) ∨ (((p5 ∧ True) → True) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48404092440354402811632030248 : (((p1 → ((False ∨ ((True ∨ p1) ∨ p3)) ∧ ((False ∧ (False ∨ p5)) ∨ ((p5 → p5) ∨ (((p5 ∧ p4) ∧ p3) → p1))))) → (p1 → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232952498844258459608058898685 : ((p3 ∧ (p4 ∨ p2)) → (((((((p3 ∨ (p5 ∧ p4)) → p1) ∨ (((True ∧ (False → p3)) → True) → p5)) ∧ p5) ∨ True) ∨ p1) ∧ (p3 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61076653726557515834006575195 : ((False ∧ (((True ∧ (((p1 ∨ False) ∨ (p5 ∧ (True ∨ (p1 → p3)))) ∧ True)) ∧ (p4 ∨ (False ∨ p1))) ∧ ((p4 ∧ p5) ∧ (p1 → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111554318410642326439107817008 : (((((((True → p3) ∨ (((p3 ∨ p3) ∨ p4) → (p1 ∧ (True → p2)))) → p3) ∧ (True → ((True → p4) ∧ p5))) ∧ p4) ∨ p1) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147374206974903826863502183072 : (((((p1 → (p4 ∨ (p5 ∧ p4))) ∧ (((p5 → False) ∨ p2) → p4)) → (p4 ∧ (True ∧ (False → False)))) ∨ True) ∨ ((p5 ∧ (False ∨ p4)) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54242778183068257086893515738 : (((((True ∨ (p2 ∧ p3)) → p1) ∧ (p1 → p4)) ∧ ((((p1 ∨ ((((p4 ∧ p1) ∨ (p1 ∨ p3)) ∨ p2) ∧ True)) ∧ True) → p4) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115891528703357182033319669293 : ((((p2 ∨ (p1 → p5)) ∨ p3) ∨ (p3 → (((p5 → (((((p3 ∨ (p3 ∨ p5)) → p1) → p4) → p3) ∨ False)) → True) → p4))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354597397578932423188990181099 : (p5 → ((((((((p1 → False) ∧ ((p4 → (((p5 ∧ p2) ∧ p5) ∨ (p4 ∧ (p3 → p1)))) ∧ p5)) → p1) ∧ p1) ∨ True) ∧ p5) ∨ p4) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749323551482713456625506724846 : (((True ∧ ((((((False ∨ p1) ∧ ((((((False → p1) → (True ∨ False)) → p1) ∨ p2) → (p3 ∨ False)) ∧ p2)) ∧ p1) ∧ p2) ∧ True) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307475826939743046121688212648 : (p1 ∨ (p5 ∨ (p4 → (((True → ((False ∧ p3) → p3)) → p1) ∨ (p3 → (((((p1 → p2) → p1) ∧ p3) ∧ p4) ∨ (p4 ∨ (p4 ∨ p5)))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682005054190126196198310583879 : ((((((p3 ∨ (p3 ∨ p3)) ∨ (p5 ∨ (p4 ∨ ((p3 ∧ p2) ∨ (p2 → (False → p3)))))) ∨ p4) ∧ ((True ∨ (False → p4)) ∨ (p2 ∨ False))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784433852311204684809725915333 : (((p3 ∨ (p4 ∧ (p4 ∧ ((((((True ∨ (p4 ∧ p2)) ∨ p1) → p5) → p1) → (p3 → (False ∨ p2))) ∧ ((p3 ∨ (p3 ∧ p4)) ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206484937222276774203633879704 : ((p5 ∨ ((p3 ∧ (p2 ∧ p1)) ∨ p4)) ∨ (((p5 → p4) ∨ (((((((False → False) ∨ p1) ∧ False) ∨ (p3 → p4)) ∧ p3) ∧ False) → p1)) ∨ False)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137674449777873084046910973580 : ((False ∨ (p4 → (((((p3 ∨ p2) → p4) ∧ ((p3 ∨ (p5 → True)) ∧ p3)) → (((True ∧ p5) ∧ p4) → p2)) → p3))) ∨ (False → (p2 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782398470634072272945360320372 : (((p3 ∨ ((((True ∨ (p4 ∧ (False → p4))) ∨ (((((False ∨ p2) → p3) ∨ p3) ∨ (p4 → p5)) → (True ∧ (p3 → p3)))) → p4) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_661837607074399072785444345509 : ((((((True ∧ (p2 → ((p4 → ((p3 ∧ (False ∧ p4)) ∨ p5)) ∨ False))) → (True ∨ p5)) → ((p3 → True) ∧ (p2 → False))) → (False ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137642841219676078157321310608 : ((False ∨ ((True ∨ (p3 → (((p3 → True) ∧ p1) ∨ (p4 ∨ p4)))) → ((p5 ∨ False) ∨ (p3 ∨ ((p2 ∧ False) → True))))) ∨ ((False → False) ∧ p5)) := by
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
theorem thm_5_vars_640077546261913891667899029387 : ((((((p4 ∧ p2) ∧ p2) → ((False ∨ (p1 ∨ p2)) → (((False ∧ ((p4 ∧ False) ∨ (p1 ∨ (p5 → p2)))) ∨ (p3 ∧ True)) ∧ p1))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53856009101896734645926252617 : (((((p2 ∧ p2) → p1) ∨ (p3 ∨ (p5 ∧ (p2 ∧ p3)))) ∨ (((((False → (p5 ∨ p1)) ∧ p5) ∧ p4) ∧ ((False ∧ p4) ∨ p1)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192939129326517312930354392530 : ((((p1 → (True ∧ p5)) ∨ (p1 ∨ p1)) ∨ (p1 → p4)) → (((False ∧ (False → p3)) ∨ p3) → (((p1 ∧ (p4 → p1)) ∧ p4) ∨ (False → True)))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h13 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166927842530715666754231971751 : (((((p5 ∨ p2) ∧ p5) ∨ ((((p3 ∧ p1) ∨ True) ∧ (p5 ∨ p2)) ∨ (p2 → False))) ∧ p3) → (p1 ∨ ((((p3 ∧ p4) ∧ p2) ∨ True) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h16 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h17 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h15
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41340351517129248396901743862 : (((((((p4 ∧ (True ∨ p3)) → (False ∧ p5)) → p2) ∧ (p5 → ((p4 ∨ p5) ∧ p4))) ∨ ((p1 ∨ False) ∧ (p3 ∧ (p5 → True)))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38550841966393804574162774523 : ((((False ∨ ((p3 ∧ p4) ∧ (p1 → (p1 ∧ (False → p1))))) ∧ (p4 → (((p4 ∨ (p1 ∧ p4)) → p5) → ((p2 ∨ p3) → False)))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64892162622770827313801407754 : ((p2 ∨ (((True → (p5 ∨ p2)) ∧ ((p5 ∧ (True → p1)) → ((False ∧ ((p1 ∧ p2) ∨ (p2 → p1))) ∧ True))) ∨ (p1 → (p5 ∨ True)))) ∨ p2) := by
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
theorem thm_5_vars_775627006513284577191901037054 : (((False ∨ (False ∨ (p1 ∨ (p2 ∨ ((False ∧ ((p4 → (p1 ∨ False)) → True)) ∨ (False → (True ∧ (p4 ∨ (((True ∧ True) → False) ∨ p5))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39970501121542603880371250658 : (((p4 → ((p3 ∧ p5) → (p2 ∨ (p2 ∧ ((False → (((p1 ∨ (p3 → (False ∧ p4))) → ((p5 ∨ p4) ∨ True)) ∧ False)) → p2))))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217923324389368650938773005607 : (((p5 → (p4 ∨ True)) → False) → (((False ∨ (((((False ∨ True) ∧ (p4 → p3)) ∧ (p2 ∧ p2)) ∧ (p3 → p1)) → (False ∧ p3))) ∨ False) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → (p4 ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p5 → (p4 ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613968113305121960512876008337 : ((((((True → ((False ∨ (p1 ∧ p1)) → (p2 ∨ (False ∨ p1)))) ∧ ((p2 ∨ False) ∨ ((True → p5) ∧ False))) ∨ ((p2 ∧ p1) ∧ p4)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113418932598085051699972666146 : (((((p1 ∧ (p3 ∧ ((p3 ∧ p4) ∨ p3))) → ((((p5 ∨ True) → ((False ∨ p1) → p4)) → p1) ∧ False)) ∧ p5) ∨ (p5 ∨ False)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171815879778489126258474704531 : (((((p1 ∨ p4) ∨ (p5 ∨ (p2 ∨ True))) → ((p4 → p2) ∧ (p2 ∨ p1))) → p4) ∨ (((((True ∧ (False ∧ p4)) → False) ∧ p2) → True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216616860879747163276108585075 : ((((True ∧ True) ∨ p3) ∧ p4) → ((True ∨ (p3 ∨ True)) → ((p1 ∧ (((p5 → p3) → p1) ∧ False)) ∨ (p3 → ((p4 ∧ p4) ∧ (p4 ∧ p3)))))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h5
      -- One of the premise coincides with the conclusion.
      exact h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h5
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h5
      -- One of the premise coincides with the conclusion.
      exact h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h5
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h1.left
      let h15 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h15
        -- One of the premise coincides with the conclusion.
        exact h15
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h15
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h21
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h15
        -- One of the premise coincides with the conclusion.
        exact h15
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h15
        -- One of the premise coincides with the conclusion.
        exact h21
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h1.left
      let h24 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h28
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h24
        -- One of the premise coincides with the conclusion.
        exact h24
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h24
        -- One of the premise coincides with the conclusion.
        exact h28
      case inr h29 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h30
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h24
        -- One of the premise coincides with the conclusion.
        exact h24
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h24
        -- One of the premise coincides with the conclusion.
        exact h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309372380970250766892695997782 : (p2 ∨ (((False ∨ True) ∧ (((p3 ∧ p3) → (((True ∨ p5) → p1) → (((False ∧ p1) → (p2 ∧ p3)) → p5))) ∨ (p3 → True))) ∨ (p2 ∧ False))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774235284077117977010243354 : (((p3 ∧ p5) ∨ (False ∧ (((p4 ∨ ((((p4 ∧ p2) ∨ (p5 ∨ p3)) ∧ (False ∨ p3)) → p3)) ∧ ((p1 → p2) → p1)) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134177254062679095470348494534 : ((((p2 ∧ (((False ∧ p2) → (True → (p2 ∧ (p4 → (p1 ∨ True))))) ∨ p5)) → ((p5 ∨ (True → p1)) ∧ p4)) ∨ True) ∨ (False ∨ (p3 ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258424900410133513495157732000 : ((p5 ∨ p1) → ((((((p4 ∨ p2) ∧ p4) → p2) → p1) → p1) → ((True → (p4 → (True → False))) → (True ∧ (p4 → (p3 ∧ (p2 ∧ False))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h13
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h16 := h14 h15
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h17 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h18 := h16 h17
    -- False on the left can always be used.
    apply False.elim h18
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h19 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h20 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h21 := h3 h20
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h22 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h23 := h21 h22
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h24 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h25 := h23 h24
    -- False on the left can always be used.
    apply False.elim h25
  case inr h26 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h27 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h28 := h3 h27
    -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
    have h29 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h28, we can now drive its conclusion.
    let h30 := h28 h29
    -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
    have h31 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h30, we can now drive its conclusion.
    let h32 := h30 h31
    -- False on the left can always be used.
    apply False.elim h32
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h33 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h34 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h35 := h3 h34
    -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
    have h36 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h35, we can now drive its conclusion.
    let h37 := h35 h36
    -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
    have h38 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h37, we can now drive its conclusion.
    let h39 := h37 h38
    -- False on the left can always be used.
    apply False.elim h39
  case inr h40 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h41 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h42 := h3 h41
    -- We want to use the implication h42 based on <expert-advice>. So we show its premise.
    have h43 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h42, we can now drive its conclusion.
    let h44 := h42 h43
    -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
    have h45 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h44, we can now drive its conclusion.
    let h46 := h44 h45
    -- False on the left can always be used.
    apply False.elim h46



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115225991499994802457900996187 : ((((((p5 ∨ False) ∨ p2) → ((p4 → p2) ∨ p2)) ∧ True) ∨ ((p2 ∨ (True → ((True → (p3 → (p3 ∨ p1))) ∧ p4))) → p1)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62141675691637141340139970382 : ((p2 ∧ (True → (((p3 ∨ (p4 ∨ (p4 ∨ ((True ∨ (p4 → (p1 ∧ False))) ∧ (p4 ∧ ((True ∨ p1) → (False ∧ False))))))) ∨ p1) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_381630263450733658976259948317 : (((((((p3 ∧ p2) ∧ ((((p4 ∨ p4) ∧ (False ∨ (False ∨ (((p2 → (False ∨ True)) → False) ∧ p5)))) ∨ p1) ∨ True)) ∧ p2) ∨ True) ∨ p4) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_486495883225624654237995747622 : ((((p3 ∧ (((p3 ∨ p3) → True) → False)) ∨ (True ∨ ((p2 ∨ p4) ∨ (((p2 ∧ p3) → p1) → ((True ∨ p1) ∨ (False ∨ (True → p3))))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185333346224954252791668295625 : ((p3 ∧ (p1 → (((p2 → (True → (p3 → True))) ∧ p3) ∨ p2))) ∨ ((p5 ∧ p2) ∨ (((p2 ∧ (((p3 ∨ True) ∧ p1) ∨ False)) ∨ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21095454684785611771233925745 : ((((p4 → True) ∧ (p4 → ((True ∨ (p1 ∧ (p2 → p2))) ∨ p2))) → (((((False → (p3 ∧ p4)) ∨ p3) → False) ∧ (p1 ∨ p3)) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157417029543296829114117191627 : ((((((p2 → False) ∧ p3) ∨ p1) ∨ (((p5 ∧ p4) ∧ (p3 ∨ False)) ∨ (False → p4))) ∧ (p3 → True)) ∨ (p4 ∨ (p5 ∨ ((p5 → p1) ∧ p2)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69080189056502229358592861308 : ((p5 → (((((p5 ∧ (True → (p3 → True))) → p5) ∧ (p2 → p1)) ∧ (((p3 ∧ False) → ((p5 ∧ (False ∨ True)) ∨ p2)) ∨ p5)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218151515228799584633802709755 : (((p5 → False) ∧ (p4 → p3)) → (p2 → ((True ∧ ((p5 → (((True ∨ p1) ∨ False) ∧ p5)) ∨ p2)) → ((p3 ∧ ((p5 → p3) ∧ p4)) ∨ p2)))) := by
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
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171782714146943950033739241334 : ((((((p4 ∨ (p2 → ((False ∧ False) ∨ True))) → True) ∨ p3) ∨ (p5 → p3)) → False) ∨ ((p5 ∨ True) ∨ ((False → (p2 → p3)) ∨ (p3 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262183820519207415333209407570 : (True ∧ (((((False → (((p1 ∧ p1) → p5) ∨ (((p5 → ((p2 ∧ (p3 → p4)) ∨ (p4 ∨ False))) ∧ p3) → p1))) → p2) → p5) → p1) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310036392041144839578033635062 : (p2 ∨ (((p4 ∨ p3) ∨ ((p5 ∨ (p4 ∧ ((p4 → p3) → (p4 → False)))) ∨ (False → False))) ∨ (((p2 ∧ p5) ∨ p1) ∧ (False ∨ (p3 ∧ p1))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688600434760721305872658730324 : ((((p3 ∨ ((p2 ∨ p2) → ((False ∨ ((p1 ∨ (True ∧ False)) ∧ False)) → (p2 ∨ p2)))) ∧ (p2 ∨ (False ∧ (p1 ∧ ((p2 ∧ False) ∧ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343853463406379814877411288001 : (p2 → (p2 ∧ (p5 → (((True → ((p1 ∧ p2) ∧ False)) ∧ (p2 ∧ ((p4 ∧ ((((p1 ∨ p4) → p4) ∨ p2) ∨ (False ∨ p2))) → p2))) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172601622274251025181253026610 : (((p5 ∧ (True ∧ p1)) → ((((p4 ∨ p3) ∨ True) ∨ True) → (p4 ∧ (True ∧ False)))) ∨ (((False → (True ∧ ((p5 → p1) → p2))) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114264720081057621728922238872 : ((((((p2 ∧ (p5 ∨ p1)) ∨ (((True ∨ False) ∧ (p1 → p1)) ∨ (p2 ∧ p5))) → p2) ∧ p3) ∧ (False ∧ ((p4 ∨ True) ∨ p3))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620427408213963215583046880397 : (((((p5 ∨ p2) ∨ (p3 ∧ (((p3 ∧ p1) ∨ ((p2 ∧ (p1 ∧ (p2 ∨ (p5 ∨ p3)))) ∧ (False ∧ p1))) ∨ (p5 ∧ (p2 ∨ p3))))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_257262334392295718488581745207 : ((p2 ∨ p3) → (((p3 ∨ p2) ∨ (((p1 ∨ (p2 → p1)) → p5) ∨ (((False → (p3 → True)) → (p5 ∧ p3)) → p4))) → (p5 → (p3 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h7 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h8 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h17 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h18 =>
        -- One of the premise coincides with the conclusion.
        exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337483125183812463919810052226 : (p1 → (((((((p2 ∨ (((p1 ∧ p2) ∨ (True ∨ p4)) ∨ p4)) ∧ p3) ∨ p5) ∨ p3) ∨ p3) ∨ (p1 ∨ False)) ∧ (p1 ∧ ((p2 → p1) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112933933447469743368042145761 : ((((p3 ∨ True) → (True ∨ ((True → (False ∧ p1)) ∧ ((p2 → p1) ∧ ((p4 ∨ True) ∨ (((False ∨ p2) ∨ True) ∨ p1)))))) → p3) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213314770904832493219029892785 : (((False ∧ (False ∨ p5)) ∧ False) ∨ (((p3 → (p4 ∧ p3)) ∨ (((p1 ∧ (p3 ∨ p5)) ∧ p5) ∧ False)) → ((((p2 ∧ p1) → p1) → p4) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : ((p2 ∧ p1) → p1) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h4
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50955195313275777442003831389 : (((((p5 ∧ p5) ∧ ((p4 → p4) ∨ p5)) ∧ (((p1 ∧ p4) ∨ ((True ∨ p1) ∨ p3)) ∧ p3)) ∧ (((False → (p1 → p3)) ∨ p2) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56541931195823031355918147494 : (((p1 ∨ (p5 ∨ (p3 → p5))) → (((False ∨ ((p2 ∨ False) ∧ (True ∨ p2))) → True) → (((p4 ∨ p4) ∧ (True → (p5 ∧ p1))) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66144366485586531627919919499 : ((p5 ∨ ((p5 ∧ ((p5 ∧ (p1 ∨ ((p2 ∧ p2) ∧ (p5 → False)))) ∧ ((((p5 ∨ p2) → (p2 ∨ False)) ∧ p3) ∨ p2))) ∨ (True ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343579270495688440447703750841 : (p2 → ((False → p1) → ((((((p4 → ((p4 ∨ p1) → (False ∧ p2))) ∧ False) → p1) ∧ (p3 ∧ ((p2 → p5) ∧ p1))) ∧ p3) ∨ (p5 → True)))) := by
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
theorem thm_5_vars_42653528056035430248542641609 : (((p4 ∨ ((True ∨ ((((p1 ∧ False) → (False → (p1 ∧ False))) ∨ p4) ∨ (p2 ∨ (True → (p2 → ((p4 ∧ p4) ∧ p1)))))) → False)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53213792253894365356481717857 : ((((((p3 → p3) ∨ True) → (p5 ∨ False)) ∨ ((p5 → p5) ∨ True)) ∨ ((((p3 ∨ True) → p4) ∨ (p5 ∨ ((True ∨ p2) ∧ False))) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312251938752696330908463758600 : (p2 ∨ (p1 → ((((True ∧ p1) → (False ∨ ((p5 ∧ p4) → False))) ∨ p1) ∧ (((p2 ∨ ((p4 ∨ True) ∧ p1)) ∧ (True ∧ p1)) ∧ (p1 ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137356114986906087626400266038 : ((p3 ∧ ((True ∧ ((p1 ∨ p3) ∧ (((p4 → (((p4 ∧ False) ∨ ((p1 → p2) → False)) ∧ True)) ∨ p4) ∨ False))) ∨ p1)) ∨ ((p1 ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177284307092633905100556884670 : ((p1 ∨ ((p3 ∨ (((p5 ∨ p3) ∨ (p3 ∨ p5)) → p5)) ∨ (p4 → p4))) ∧ (p1 → ((p5 ∧ (p1 → (p3 ∨ p3))) → (False ∨ (p2 → True))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112174727290868530877326649677 : (((p4 ∧ ((p2 → (((p3 ∨ (p4 ∨ ((False → p4) ∨ ((True ∨ p3) → p1)))) → (p2 → p4)) ∨ (False ∨ True))) ∨ p2)) ∨ True) ∨ (True ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263929541273363993364021004957 : (True ∧ (((p3 ∧ p1) → (p3 ∨ (p3 ∨ (((True → (p2 ∧ p1)) → p4) ∨ True)))) → (p2 ∨ (((p4 ∨ p2) ∨ ((p1 → p1) → p5)) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204931245662685303774774838027 : ((((False ∧ True) → (p3 → p3)) → p5) ∨ (p5 → ((p1 ∧ (p5 ∨ ((False → p3) ∧ p5))) → (True ∧ ((p1 ∨ (p2 → p4)) → (p4 ∨ True)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h2.left
    let h13 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113534030191063146321011035298 : ((((((p3 ∨ (p5 ∧ p5)) ∨ True) → p5) → (True ∧ (((p2 ∧ p4) → ((True ∧ False) ∨ p5)) ∨ (p3 → False)))) ∨ (False ∨ p2)) ∨ (p1 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : ((p3 ∨ (p5 ∧ p5)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187010891471218453468448765927 : (((True ∧ (p5 ∧ p4)) → (True ∧ (p1 ∧ ((p1 ∨ p3) ∨ False)))) → (True ∧ ((((p3 ∧ (False ∨ p2)) ∧ p3) ∧ (p2 ∨ p4)) → (p1 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259800027509738430357506957066 : ((p1 → p3) → ((p2 → (p3 → (True ∧ ((((p2 → True) → ((((False ∧ True) → p2) ∧ p5) ∧ p1)) ∧ False) ∨ (p5 → (p1 → p1)))))) ∨ False)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346605672265304759248897805519 : (p3 → ((((p1 ∨ p4) → ((((p3 ∨ ((p4 → (p4 ∧ True)) ∧ p3)) ∧ p2) ∨ (p5 → True)) ∨ p3)) → (p4 ∨ p1)) ∨ ((True ∨ p3) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155383278762958808257362211824 : ((((p5 → (p3 ∨ p4)) ∧ p3) ∨ ((False ∨ p3) → (True → ((p2 → (p4 ∧ False)) ∨ (False → True))))) ∧ (True ∨ (((p5 ∨ False) ∨ p2) ∧ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610125988537842512347064590473 : ((((((p1 ∨ (p4 → (((p4 ∧ p3) ∧ (False ∨ ((p1 ∧ (((p1 → p1) → p1) ∧ p1)) → p5))) ∨ (False → p3)))) ∧ p4) → p1) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746139936906001348389493379439 : ((((p1 ∨ p2) → (((((((((p1 → p4) ∧ p4) ∨ False) ∨ True) → p1) → ((p1 ∧ p4) ∨ True)) ∧ (False ∧ False)) ∨ (p1 → True)) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37080299709329910842846651901 : ((((((((((p3 ∨ p3) → (p3 → (False → p4))) ∧ ((True → p4) ∧ (True → p5))) ∨ True) ∧ p4) → (p4 → False)) ∨ p3) ∧ p1) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230562942175006266759445998647 : (((p1 → True) ∧ p2) → (((True → p2) → p3) ∨ ((p3 ∨ p2) → ((((p3 ∧ (p5 ∨ p2)) ∨ (p2 → p3)) → ((p5 ∨ True) ∨ True)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160141567111907344661443870207 : (((((True ∧ ((p1 → (True ∧ (p4 → True))) ∨ p1)) ∨ ((p5 ∧ True) → p1)) → False) ∧ (p4 → p4)) → (((p5 ∨ (p4 ∨ p3)) → p4) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((True ∧ ((p1 → (True ∧ (p4 → True))) ∨ p1)) ∨ ((p5 ∧ True) → p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h5
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166743396058433458188349751486 : ((p4 → (((((p5 ∨ (p3 ∨ p5)) ∨ p3) → (p4 → False)) ∧ p2) ∨ (p2 → (p5 ∨ p2)))) ∨ (p4 ∨ (p4 ∨ (((p2 ∨ p2) → p5) ∧ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174647475146680835819424018926 : ((((p4 → p4) ∧ True) ∧ (p3 ∨ (((True ∧ True) ∨ (False ∧ (True ∨ p2))) ∨ p5))) → (((p2 → False) → p2) ∨ ((False → False) → (p5 ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- False on the left can always be used.
        apply False.elim h15
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253723227695435763581609181812 : ((p1 ∧ p1) → (((p4 → ((p4 ∧ (p2 ∧ p1)) ∧ (((False ∧ (p2 ∧ ((p5 ∨ True) ∧ p3))) → True) ∨ ((False ∨ p5) ∨ p2)))) → p4) ∨ True)) := by
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
theorem thm_5_vars_304739784603174026936601723229 : (p1 ∨ (((p2 ∧ ((False ∨ p3) ∧ p2)) ∧ ((True ∧ (True ∨ p3)) ∧ ((p5 → (p3 → (False → ((p4 → p4) ∧ p3)))) → p2))) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808527333378884063472959645928 : (((p4 → (p5 ∨ ((((p4 ∧ ((p1 → ((p5 → (p2 ∧ (p1 ∨ (p2 → False)))) ∨ ((p1 → p4) → False))) → False)) ∨ p3) ∧ p2) ∨ True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53875508853882137515536369425 : ((((p1 ∨ p2) ∨ (p3 → (((False ∨ p2) ∧ p4) ∨ p1))) ∨ (((((True ∧ p1) ∧ ((p5 → p2) → True)) ∨ (p4 ∧ p1)) ∨ False) → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348813305910140160346801088536 : (p3 → (p1 ∨ ((p2 → (False ∧ ((p5 ∨ p2) ∨ (True → p1)))) ∨ ((p3 ∧ ((p2 → (((p2 → (p1 → p5)) → p4) ∧ False)) ∨ True)) ∨ p4)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136787815108185921405322242261 : (((False → p5) ∧ ((p5 ∧ True) → (p2 ∨ ((p2 ∧ ((p4 ∨ (p1 ∧ ((p1 → p3) → p1))) ∧ (p3 ∨ p1))) ∧ False)))) ∨ ((p3 ∨ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190038372644179335726370981746 : ((((((p5 ∧ p1) ∨ (True ∧ p4)) → p1) ∨ True) ∧ p1) ∨ ((((p4 ∧ p5) ∧ p5) → p4) → (((False ∧ True) ∧ (p3 → p2)) ∨ (True → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178002251338420701167898158604 : (((p2 ∨ (((False ∨ True) ∧ ((False → False) ∧ p4)) ∨ (p4 ∧ p5))) ∨ True) ∨ ((p5 ∧ (((p3 ∧ p1) → False) ∨ (p1 ∨ (p1 ∧ p1)))) ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800012662960202658731547805106 : (((p2 → (((((p5 → False) ∨ False) ∨ ((True ∧ ((p5 → ((p4 ∨ p3) ∧ False)) → True)) ∧ (False ∧ True))) ∧ ((p5 ∨ p1) ∨ True)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258002421666674929689542045174 : ((p4 ∨ p1) → ((((p5 ∨ p1) ∨ p2) ∨ p5) ∨ (p1 → ((((p5 ∨ (p1 ∧ (False ∨ p5))) ∨ (p1 ∧ (p5 ∨ (False ∧ p3)))) ∧ p2) → p1)))) := by
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
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- False on the left can always be used.
          apply False.elim h12
        case inr h13 =>
          -- One of the premise coincides with the conclusion.
          exact h3
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- False on the left can always be used.
        apply False.elim h19
  case inr h21 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208958037880880863134414352347 : ((True ∨ ((p3 ∧ (p4 ∧ p1)) → p2)) → (((p4 → (p3 ∧ (p5 ∧ ((((p3 ∧ (p1 → p1)) ∨ (p1 ∧ p5)) ∧ True) ∧ p5)))) ∨ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49150233478065092560766928636 : ((((p1 ∧ ((p5 ∨ p3) ∨ ((p1 ∨ p3) ∨ p1))) ∧ ((((p2 → p3) ∧ p1) → (p1 ∧ (p4 ∨ False))) ∨ False)) ∨ (p5 ∧ (p2 → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157075702816030249037541256766 : (((p2 ∨ ((p5 ∧ (((((((p1 ∧ p5) ∨ p2) → p1) → p3) ∨ p5) → p4) ∨ p3)) ∨ p3)) ∨ p3) ∨ (((p4 ∧ (p3 → True)) ∨ p4) → p4)) := by
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
theorem thm_5_vars_39394216441666700152490979006 : (((p4 ∧ (((True → (False ∧ p5)) → ((p1 ∨ ((p2 ∧ p4) → ((((p3 ∨ True) → (p2 ∧ p1)) ∧ p1) ∧ True))) ∧ p5)) ∧ True)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



