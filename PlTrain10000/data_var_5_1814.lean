variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802574092483021550800017607964 : (((p2 → (p5 ∨ (((p5 ∨ (((p4 → p1) → True) ∧ p5)) ∨ (True → (p1 → ((p2 → ((p5 ∨ p3) ∧ (True → p1))) ∧ p4)))) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116153199675137950296196070629 : (((p2 ∨ (True ∧ p4)) ∧ (p1 → ((p2 ∧ ((True ∧ p3) ∧ (((False ∧ p2) → (True ∧ p4)) ∨ p2))) → ((p1 ∧ False) ∧ p5)))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784686099752531436771729054609 : (((p3 ∨ (p4 ∨ (((((p3 → False) ∨ p4) ∧ ((False ∨ (False ∨ False)) ∨ ((p3 → p3) ∨ ((False ∧ (p2 ∧ False)) → p1)))) ∨ p3) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350064842847241786924393812972 : (p4 → ((((((True → p1) ∧ (p1 → (p4 ∧ (p4 ∧ (((p1 ∨ (p3 ∧ (p1 ∨ p5))) → p2) ∧ p5))))) ∧ p2) ∨ False) ∨ (p3 ∧ p1)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344955343923411206255465965515 : (p3 → (((p1 ∧ (((p4 → ((p3 ∨ p5) → (((p1 ∧ ((((p2 → p3) ∨ True) ∨ p4) ∧ p2)) ∨ False) ∨ True))) → p2) → p2)) ∨ p3) ∧ p3)) := by
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
theorem thm_5_vars_709774211413546476592508364468 : ((((p1 → (p4 ∧ (p2 ∨ (p4 ∧ (False → p4))))) → ((((p1 → (p4 → p2)) ∧ (p1 ∨ (True → p3))) ∨ (True → False)) → (False ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355538154928845174635767299232 : (p5 → ((((((((p3 ∧ ((p5 → p3) ∧ p4)) ∨ p5) ∧ (p5 → ((p5 → (p2 ∨ True)) → False))) ∨ p1) ∨ p5) ∨ p3) ∨ p4) ∨ (True → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342670635682852581515936831012 : (p2 → ((p1 ∧ (p2 → ((p1 → p3) ∧ ((False ∨ p3) → p1)))) ∨ (((p2 → ((True ∨ True) ∧ p1)) ∧ ((p2 ∨ p3) → p5)) ∨ (p5 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156950267680698378533310096258 : ((((p4 ∨ (p4 → ((p3 ∧ p3) ∧ ((p3 ∧ ((p3 ∧ False) ∨ p3)) ∨ p2)))) → (p3 ∨ p4)) ∨ p4) ∨ (((p1 → (p1 ∨ False)) ∨ False) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138994130980227792468884365899 : (((((p1 ∨ (p1 ∨ (((p5 ∧ ((True → p4) ∨ p4)) ∧ (True ∨ p5)) ∧ p5))) → (p2 ∧ (p4 → p2))) ∨ p1) ∨ False) → (p2 ∨ (True ∨ False))) := by
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
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206961944893133416408465497810 : ((((p3 ∧ (True ∧ p3)) → p5) ∧ p1) → (((p1 → ((p3 → False) → False)) ∨ (p2 ∧ p5)) ∨ (p1 ∨ (p1 ∧ (((p1 ∧ False) → p4) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226138570956167004212158995108 : (((False ∨ p3) ∨ p3) ∨ (p4 ∨ (p2 ∨ (((False ∧ (p3 → True)) ∧ False) → (True ∧ (((p5 ∧ (p3 ∨ ((p4 ∨ p4) ∨ p1))) → False) ∧ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h1.left
        let h14 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h15 := h13.left
        let h16 := h13.right
        -- False on the left can always be used.
        apply False.elim h15
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h1.left
        let h19 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h20 := h18.left
        let h21 := h18.right
        -- False on the left can always be used.
        apply False.elim h20
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h1.left
      let h24 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h25 := h23.left
      let h26 := h23.right
      -- False on the left can always be used.
      apply False.elim h25
  -- Conjunctions on the left can always be decomposed.
  let h27 := h1.left
  let h28 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h29 := h27.left
  let h30 := h27.right
  -- False on the left can always be used.
  apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798261954549722969585608565516 : (((p1 → ((p2 ∧ (((((False ∧ False) ∨ p4) → ((p4 → (False → p1)) ∨ p2)) → p2) ∨ False)) ∨ (p5 ∨ (p1 ∨ (p1 → (p3 → p1)))))) ∨ p4) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159371746008433454771280339890 : ((((((p1 → (False ∨ True)) ∨ (((p3 ∧ p2) → (p1 → True)) ∧ True)) ∧ (p5 ∨ p5)) ∨ p2) ∧ p2) → (((p1 ∧ (False ∨ False)) ∧ p3) ∨ p2)) := by
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
      cases h6
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136275752117508340762944822079 : (((((p2 ∧ False) ∨ p3) ∨ (True ∧ p5)) → (((((p4 ∨ (True → (p3 → True))) ∨ True) ∧ False) ∧ p3) ∨ (True ∧ False))) ∨ ((p5 ∨ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60269462940185496517861755267 : (((False → p3) → ((p5 ∧ (((False → False) ∨ p2) ∨ p1)) → (p1 ∧ ((((p2 ∨ (p3 ∧ (p4 ∨ True))) ∨ p4) → (True ∨ p4)) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340106603101049555060086402655 : (p1 → (p3 → ((False ∧ (((p5 ∧ (((p1 → ((p3 → p2) ∨ (True → False))) → p2) ∧ True)) ∧ p2) → p4)) ∨ (((p1 → True) ∨ p2) → True)))) := by
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
theorem thm_5_vars_256006497196870363904830193539 : ((True ∨ p3) → ((False → p3) → (((p5 → p2) ∧ ((p3 → False) ∨ (p5 ∧ p2))) ∨ ((False ∨ ((True ∧ False) ∧ p3)) → (p5 → (False ∧ p4)))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- False on the left can always be used.
      apply False.elim h11
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h14.left
      let h17 := h14.right
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h19
    -- Implications on the right can always be decomposed.
    intro h20
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Conjunctions on the left can always be decomposed.
      let h25 := h23.left
      let h26 := h23.right
      -- False on the left can always be used.
      apply False.elim h26
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h27 =>
      -- False on the left can always be used.
      apply False.elim h27
    case inr h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h29.left
      let h32 := h29.right
      -- False on the left can always be used.
      apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313018131232702886864447760054 : (p3 ∨ (((True ∧ ((False ∧ (((((False → p3) → p1) ∧ (p5 ∨ (True → False))) → p4) ∧ (p5 ∧ (p1 ∧ p2)))) ∨ (False → True))) ∨ p3) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_61228412457839005144827493866 : ((False ∧ (p1 ∧ (p5 ∨ ((((((True ∨ p1) ∧ p2) → ((p5 ∧ (True ∨ p3)) ∨ True)) ∧ p5) → (p2 ∧ (True ∧ p1))) ∨ (p2 → True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618042722297852745632800766474 : ((((((True ∧ (p5 → p4)) → p5) ∧ (p3 ∧ (((((p1 ∨ (p1 ∧ p5)) ∧ p5) ∨ p1) ∧ (((p1 → p5) → False) ∧ p1)) ∧ p5))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_64251435893300625936180989194 : ((False ∨ (p3 ∨ ((p5 ∨ (p2 ∧ ((((p1 ∨ p1) ∧ (p5 ∨ False)) → ((((p4 → p2) ∧ p1) ∨ p3) ∧ p3)) → p2))) ∧ (p5 ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244189567893019328076937404545 : ((True ∧ p5) ∨ (((((p3 ∨ ((p1 ∧ p5) ∨ p3)) ∧ ((p4 → True) ∧ (p4 ∧ True))) ∨ False) ∧ (False → ((p4 → (p2 ∧ p2)) → False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672568728646957391135261598300 : ((((((p4 ∨ ((p5 ∨ ((False ∨ p3) ∧ p2)) → (p4 ∨ p5))) ∧ (((p1 → p5) ∨ True) ∨ True)) ∧ (p1 → p1)) → (False ∨ (p3 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149087223322726102326987597553 : (((p1 ∧ (p1 ∨ p2)) → (((p3 → p3) → p3) ∧ ((p5 ∨ p2) ∧ (((p3 ∨ p5) ∧ (p4 → p2)) ∧ p3)))) ∨ ((p4 → True) ∨ (p4 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736685871352669426269961877928 : ((((p2 → True) ∧ (p1 → (((((False ∨ p5) ∨ p3) → ((p3 ∧ p3) ∧ (False ∨ p5))) ∨ True) ∨ ((p5 → False) ∨ ((p1 ∨ p3) ∧ False))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117812499309197425848007060038 : ((p4 ∧ ((p5 → p4) ∧ ((p1 → (p2 ∨ (p4 ∧ (True ∧ (p5 → ((((True → True) → p1) ∧ p3) → p4)))))) ∨ (p5 ∨ True)))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187160808337367781103625587996 : (((p4 → False) ∨ ((True ∧ (False ∧ p4)) → ((p2 → p1) ∨ p2))) → ((p1 → ((p5 ∧ (p4 ∧ p1)) → (p2 ∨ (p2 ∧ (True → False))))) ∨ True)) := by
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
theorem thm_5_vars_249749324119621339542335274790 : ((p5 ∨ p5) ∨ ((p1 ∨ p4) ∨ ((False ∨ (((False → ((p5 ∨ (p4 → p2)) → ((p1 ∨ (p5 ∧ p4)) → p2))) ∨ p2) ∧ p4)) ∨ (p3 → True)))) := by
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
theorem thm_5_vars_602615802817137253555670205513 : ((((False ∨ ((False ∧ (p1 ∧ (((((False ∧ p2) ∨ ((((p5 ∧ p3) ∨ p3) ∧ p3) ∨ p3)) ∨ p5) ∨ p4) ∨ p1))) ∧ (p4 ∨ p2))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708537525139952684730418371339 : ((((((p3 ∨ (p2 ∧ p3)) ∧ (p2 → p1)) ∨ p3) → ((True → (p5 ∨ p5)) → ((p3 ∨ ((p1 ∨ p2) ∨ ((p4 ∨ True) ∨ p1))) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56293781967029199307550860101 : (((((p4 ∧ p5) ∨ p2) ∧ p2) → ((False ∨ False) ∧ ((p3 → False) ∨ (True ∧ (((p3 ∧ p5) ∧ (((p2 ∨ p2) → p5) → p2)) ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46988987826400106814722251183 : (((((p1 ∨ (((p3 ∨ (True → (p1 ∨ p2))) ∨ (p5 ∧ False)) → p1)) ∧ ((p3 → p1) ∧ ((p4 ∧ True) ∨ p3))) → False) ∨ (False → False)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172733129973548226546598849289 : (((p3 → False) ∨ ((p1 ∧ (p2 ∧ True)) ∧ (((p3 → True) → p1) ∨ (p1 → False)))) ∨ (False → (((p3 ∨ ((p5 → p2) → p3)) ∧ True) → False))) := by
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
    apply False.elim h1
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168353888381120091434456583905 : (((p5 ∧ True) ∨ (((p5 ∧ (p3 ∨ ((p4 → p5) → (p2 ∨ p2)))) → (p2 → p5)) ∨ True)) → (p5 ∨ (((p2 ∨ False) ∨ p4) ∨ (p5 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356924348510201610138743172523 : (p5 → ((p2 → ((True → p2) ∨ p4)) → (((((p5 → (p1 → False)) → (p3 → False)) ∧ (((p2 ∧ p4) ∨ p5) → False)) ∧ (p2 ∧ p3)) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h10 : ((p2 ∧ p4) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h11 := h7 h10
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312107130972465078659811566948 : (p2 ∨ (True → (((p4 ∧ (False ∨ (((p4 ∧ ((p1 ∨ ((p3 → p4) → (p5 → (p3 ∨ p2)))) → True)) ∧ p3) ∧ (p4 ∧ p1)))) → p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194042650812492138762361328307 : ((p5 ∨ ((((p4 ∨ p2) ∧ p2) ∧ True) ∨ (p5 ∨ p1))) → (p3 ∨ (((p4 ∨ (True ∨ (p4 ∨ (p1 ∨ (p2 → False))))) ∨ p5) ∨ (True ∨ p3)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753547523841248520215749684067 : (((False ∧ ((True → ((p2 → (p1 → ((p2 ∨ True) → p3))) ∧ ((p4 ∨ p3) → (True ∨ (p5 ∧ p3))))) ∨ ((p2 → p2) → (p4 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37955541755372802117975010978 : (((((p5 ∧ (p4 ∨ (True → (((False → p5) ∨ p4) → (False → ((True → ((p1 ∨ True) → p1)) ∨ p3)))))) ∧ p5) ∨ (p2 → p4)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175031753000620610259792144441 : ((p1 ∧ (p1 ∨ (((((p1 ∧ True) → p5) → (True → p2)) → p4) ∧ (p3 → p5)))) → (p4 ∨ ((p4 → (True ∧ ((True ∧ p2) → p4))) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321052856991220262500162407443 : (p4 ∨ (p1 ∨ ((p1 ∨ ((((((p5 ∨ (p1 → p3)) ∨ (p3 ∨ (p2 → (p3 → p1)))) → p5) ∨ False) ∨ (p1 ∨ False)) ∨ (True → True))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111882984558026867432360716064 : ((((False → (((p1 ∧ (p3 ∧ (p5 ∨ (True ∨ (p3 ∧ (p4 ∧ p5)))))) ∨ True) ∨ True)) → ((p4 → (True → p1)) ∧ p3)) ∨ p2) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209297881046918566176643445084 : ((True → (False ∧ ((p3 ∨ p1) ∧ False))) → ((p5 ∨ (p3 ∨ False)) → (False ∧ (False ∨ (p1 ∧ (False → (((p3 ∧ p3) ∧ (p2 ∧ p5)) ∨ False))))))) := by
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
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h10 := h1 h9
      -- We need to get the left conjuct of h10 based on <expert-advice>.
      let h11 := h10.left
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h13 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h15 := h1 h14
    -- We need to get the left conjuct of h15 based on <expert-advice>.
    let h16 := h15.left
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h19 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h20 := h1 h19
      -- We need to get the left conjuct of h20 based on <expert-advice>.
      let h21 := h20.left
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- False on the left can always be used.
      apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198875457584295946539692933509 : ((p2 → (p1 ∧ (((True ∧ p3) ∨ False) ∧ p5))) ∨ (((False ∨ ((True → p2) ∨ p3)) ∨ ((False ∧ ((p5 ∨ False) → p5)) → p1)) ∨ (False ∨ False))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60222746237910862964879912706 : (((True → p2) → (((p5 ∨ False) → ((p3 → (p4 ∧ p4)) → ((p4 ∧ (((p2 ∧ True) ∧ p1) → ((p2 ∧ p3) → p1))) → p1))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60512945159623740341021937389 : ((True ∧ ((False ∨ (p4 ∧ (p3 ∧ (((True ∨ False) → ((p2 ∨ p4) ∧ (((p5 ∧ (p4 → p5)) ∧ (p4 → p3)) → True))) ∨ p5)))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_583838519553065070773737580448 : (((p5 → ((p4 → (((p2 ∨ False) → (p2 ∨ (p3 ∨ p4))) → False)) ∨ (((True → p1) ∨ p5) → (False → ((False ∨ (p2 ∧ p1)) ∧ p5))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346588857489653217808448354466 : (p3 → ((((p1 ∧ ((p5 ∨ (((p2 ∨ (False → p4)) → (p5 ∨ p5)) ∧ p5)) ∨ ((p4 ∧ p2) ∨ p3))) ∧ p4) ∨ p5) ∨ (p1 → (p1 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741317215384249269199926251501 : ((((p4 ∨ p5) ∨ (((p1 → p5) ∨ p3) ∧ ((False ∨ ((p1 ∨ (((((p2 ∨ False) ∧ p2) ∨ p4) → False) ∧ (p5 ∧ False))) ∨ p5)) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8301866916914013360502963700 : (((((False ∨ ((p2 ∨ ((p2 → p1) → True)) → (((False ∨ (False ∧ p1)) → False) → (True → (p2 ∨ p3))))) ∨ (p4 → p4)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303764687257044144071693864685 : (p1 ∨ ((((((False → p1) → (False ∨ p2)) ∨ p5) ∧ (((((p2 → p4) ∧ p1) ∧ (p1 ∨ p5)) → True) ∧ ((p5 → False) → p1))) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810237740717053334682219776147 : (((p5 → ((p2 ∨ (((True ∧ (p5 ∨ p2)) → False) ∧ (p5 ∧ ((False ∧ p2) ∨ p3)))) ∨ ((True ∧ (p4 ∧ False)) → (p2 ∨ (p4 ∧ p4))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116052292110032496019405864327 : (((p3 → (p4 ∧ (p5 ∧ True))) → (((p5 → ((False ∨ (p4 → p1)) ∧ False)) ∨ p4) ∨ ((False → (p2 → p2)) ∨ (False ∨ p1)))) ∨ (p1 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342873695806578173983970220388 : (p2 → ((p1 ∨ ((p3 ∧ True) → (p5 ∧ True))) ∨ (((p5 ∨ False) ∨ p5) → ((((p3 ∨ (p2 ∧ (False ∨ (p5 → p1)))) ∨ p4) ∧ True) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184363910922134671921487584745 : (((p2 ∨ ((p5 ∧ (((p3 ∧ False) → p4) ∧ p4)) → True)) → p3) ∨ ((((p4 ∧ ((False ∨ (p5 → p4)) → False)) ∨ False) → p3) ∧ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (False ∨ (p5 → p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h5
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185167757422487518752986182910 : (((False → p1) → (p5 ∨ ((p1 ∧ (True ∨ (p4 ∧ p3))) ∧ False))) ∨ ((((((p3 ∧ p5) ∨ p4) → True) ∧ False) ∧ ((p4 → p2) ∨ True)) → p2)) := by
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
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67542518403272526713188761280 : ((p1 → ((p1 → (p5 ∧ p3)) ∧ ((False → p3) ∧ ((((p5 → False) ∨ ((False ∨ (p2 → p3)) ∨ p4)) ∧ p4) ∧ (p4 → (p1 ∧ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158142912285225504641276486005 : ((((p3 ∨ p5) ∨ (p5 ∨ False)) ∨ ((((p2 ∨ p5) ∨ p2) → (p3 → ((p1 ∨ p3) ∨ p3))) ∨ p3)) ∨ ((p4 → p5) → (p3 → (p5 → False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68203225671874751474939694366 : ((p3 → ((p5 ∧ (p1 ∨ (p1 ∧ ((((p3 → p3) ∨ ((False ∧ p4) ∨ p2)) ∧ (p4 ∧ ((p3 ∧ False) → p1))) ∧ (p3 ∨ p3))))) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299362113635873092368475510991 : (False ∨ (((p5 ∨ p1) ∧ (True → ((p5 → (((p3 ∧ ((False → p5) → (False → p1))) → ((True → True) ∧ (p4 ∨ p1))) ∧ True)) → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215137500616019537416231195958 : (((p4 → p4) → (p5 ∨ p1)) ∨ (True ∨ (((p2 ∧ p3) ∨ (p3 ∨ ((True ∨ False) → p1))) ∨ (p1 ∨ (((p4 ∨ p3) ∧ p4) ∧ (False ∧ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62377681770349075886306346082 : ((p3 ∧ (((((((p2 ∨ (p4 → True)) ∧ True) ∨ (False → p1)) → True) → p3) ∧ True) ∨ (p5 → (p1 ∨ ((False ∨ True) ∨ (p3 ∧ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779935699274753379678966849434 : (((p2 ∨ (((((((True ∧ ((p1 → (p5 ∧ False)) ∧ True)) ∧ (True → True)) ∧ p1) ∧ p2) ∨ True) ∧ (p2 ∨ (True ∨ False))) ∧ (p1 → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135084469248969388959276505965 : (((((True ∧ (p5 → ((p5 ∧ p3) ∧ (p3 → (False ∧ p2))))) → False) ∧ (p5 → (p2 ∧ (p3 → p5)))) ∨ (p4 ∨ True)) ∨ ((p2 ∧ True) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695035853449522380116636019936 : (((((p1 ∧ (((p2 ∨ ((p3 ∨ p4) → (False ∨ False))) ∨ p4) → False)) ∧ p5) → (p3 ∧ (p5 → ((p4 → ((p3 ∨ False) → p4)) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191039107090709156174028595158 : (((((p5 ∨ p4) ∨ p1) → True) → (False ∨ (p5 ∧ p1))) ∨ (p3 → ((((True ∧ False) ∨ True) ∨ p2) ∨ (p5 ∧ (False ∨ ((p2 → p1) ∧ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171953980055869431648978118309 : (((((p2 → p3) → (False ∧ False)) ∨ ((p3 → (False ∧ False)) → p2)) ∧ (True → False)) ∨ (p4 ∨ (True ∨ (((p1 → p1) → p2) ∧ (True ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352798141110998875982224974129 : (p4 → ((p2 ∨ p2) → ((((((((False → False) → (p1 → False)) ∧ p5) → False) ∨ (p5 ∧ True)) ∨ False) → False) ∨ (True ∧ ((False → p2) → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616493342452229142461473876495 : (((((p2 ∧ (False ∨ (p5 ∨ (((True ∧ p5) ∧ True) ∧ (p1 ∨ p1))))) → (((p3 ∨ (p4 ∧ (p1 ∨ False))) ∨ p3) ∨ (p1 → p2))) ∨ p2) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- One of the premise coincides with the conclusion.
        exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119122196915907517349944234145 : ((p1 → (p1 ∧ (p2 ∨ (((False ∧ ((((((p2 → p1) → p4) ∨ ((p2 ∧ p3) ∧ False)) ∨ p3) → p2) → p3)) ∧ p1) ∨ True)))) ∨ (p5 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52775381752330532789298427242 : ((((((p5 ∨ p3) ∧ (True ∧ True)) ∨ (p2 ∨ (False ∨ p3))) ∧ (p5 → True)) → ((p4 ∨ p1) → ((p3 → p1) ∨ ((p2 → p2) ∨ p1)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h8.left
        let h11 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h12
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h8.left
        let h15 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h16
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h19
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- False on the left can always be used.
          apply False.elim h21
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h23
          -- One of the premise coincides with the conclusion.
          exact h23
  case inr h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h1.left
    let h26 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h29.left
        let h32 := h29.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h33 =>
        -- Conjunctions on the left can always be decomposed.
        let h34 := h29.left
        let h35 := h29.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h24
    case inr h36 =>
      -- Disjunctions on the left can always be decomposed.
      cases h36
      case inl h37 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h38 =>
        -- Disjunctions on the left can always be decomposed.
        cases h38
        case inl h39 =>
          -- False on the left can always be used.
          apply False.elim h39
        case inr h40 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661355397490214376092792503477 : (((((((((p5 → p4) → False) → False) ∧ p5) → ((p1 → (p2 → (p5 → (p2 ∨ p5)))) ∧ (False → p3))) → (True ∧ p4)) → (p4 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137749638291361462714197606284 : ((p2 ∨ (((((p1 ∨ ((p5 ∨ p2) ∨ ((p2 ∨ p2) → ((True → (True ∧ False)) → p3)))) → p5) ∨ True) → p5) ∨ p3)) ∨ (False → (p4 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111243638980596808143938387201 : ((((p2 → p1) ∧ ((p1 ∨ p4) → (((((((False ∧ False) → True) ∨ (p1 ∧ (p5 ∧ False))) ∧ p2) ∨ False) ∧ p1) ∧ p2))) ∧ p1) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42052541917610511066899301058 : ((((p1 ∨ p4) ∨ (((p3 ∨ p3) ∨ p1) ∨ (True ∧ ((False → (p4 → p3)) ∨ ((p5 ∨ p5) → ((p3 ∨ (False ∧ p2)) → p2)))))) ∨ p5) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622593966386329102286938791737 : ((((p4 ∧ (((((((p2 → (False ∨ p2)) ∧ p4) ∨ ((p2 ∨ (p4 ∧ p5)) → p5)) ∨ (p3 ∧ p3)) ∧ (p5 ∨ p5)) → True) → p3)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_65646342949334130230455670047 : ((p4 ∨ (((p1 ∨ p2) ∧ (p4 → (((p2 ∧ (((p4 → (True ∧ p1)) ∨ p2) → ((p2 → p3) → p2))) ∧ (p4 ∨ p2)) ∨ False))) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111408489817276616852185749724 : (((p2 ∨ ((p3 → p3) ∧ ((((((False ∧ False) ∧ (p2 → (p3 ∧ (False ∨ p4)))) → p4) ∨ p1) ∧ (p4 ∧ p5)) ∧ p3))) ∧ p2) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308328882847645312726792224541 : (p2 ∨ (((((((False → (p1 ∨ p2)) → (((p3 ∧ True) ∧ False) ∧ p1)) ∨ p2) ∨ (p4 ∨ ((p1 → p2) ∨ (p3 ∧ False)))) ∧ False) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228204161580782233311185874106 : ((p5 ∧ (False ∨ True)) ∨ ((False ∨ ((p3 → ((True ∧ p1) ∨ (p5 → (p5 → ((((True → p4) ∧ False) ∧ True) → p1))))) → (p5 ∧ False))) → p1)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (p3 → ((True ∧ p1) ∨ (p5 → (p5 → ((((True → p4) ∧ False) ∧ True) → p1))))) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- False on the left can always be used.
      apply False.elim h12
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h4
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114943878896086107157466700500 : ((((p1 ∨ (p1 ∨ p5)) → (((p1 → p5) → p2) ∨ (p3 ∨ (p4 ∨ p2)))) → (True → (p4 → ((False ∧ False) ∧ (p2 ∧ p2))))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802999827978689300065392494075 : (((p3 → ((((p3 ∧ (((False ∨ (p5 ∧ p1)) ∨ p1) ∧ True)) → ((p5 → True) → (p5 ∨ p2))) ∧ (p5 ∧ (p2 ∨ (p5 ∧ p5)))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320456813036809932173708187194 : (p4 ∨ ((True → True) → (((p4 ∨ (((p5 → p3) ∧ (p4 ∧ (True ∧ p2))) ∨ (p4 ∧ p2))) ∨ ((p5 ∧ (p4 ∨ p5)) → p5)) ∨ (False ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201092898394893524184885196561 : ((True → ((((p4 ∨ p1) ∨ False) ∧ p1) ∧ p5)) → (p1 ∨ ((p1 ∧ (p5 ∧ ((p5 → p2) → p2))) ∧ ((p2 ∧ p1) ∧ (p1 → (p3 → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805028877023424133051461166901 : (((p3 → ((p4 → True) → (((False ∧ False) ∨ (((False → ((p5 ∨ False) ∨ (p1 ∧ p1))) → p1) ∨ ((p1 ∨ (p3 ∧ p4)) → False))) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254224449483347377108154997363 : ((p2 ∧ p2) → ((((((True ∨ (p1 ∨ False)) ∨ False) → (p1 ∧ (p3 ∨ (p1 → ((p3 ∧ p3) ∨ p5))))) ∧ p5) ∨ p2) ∨ (p1 ∨ (p3 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650133486090543466408419270199 : ((((((False → ((p3 → (((p4 ∧ True) ∧ False) → p5)) ∨ ((True ∧ p1) ∧ p4))) → p2) ∧ (False ∧ (p3 ∨ (p3 ∧ p4)))) ∧ (p3 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113412015341679034362490052774 : ((((((True → (p5 ∧ ((((p4 ∧ p4) ∧ p5) ∨ (p4 ∨ p1)) ∧ (p2 ∨ p1)))) → (p4 ∧ True)) → False) ∧ p2) ∨ (False → p2)) ∨ (p3 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50401916747316401979342371765 : ((((p5 → True) → ((((p4 ∧ p5) ∨ (p2 ∧ p2)) ∨ p2) ∨ (False → (((p5 → p3) ∧ True) ∧ p3)))) ∨ (False ∨ ((p5 ∨ False) ∨ p4))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116529095765776677596339225863 : (((True ∨ False) ∧ (p4 ∨ (p2 ∧ (((p4 ∧ (False ∧ p1)) → p3) → (p3 ∨ (((True ∨ p2) ∨ ((False → False) ∨ True)) ∨ p4)))))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61044179340655256708392822182 : ((False ∧ ((p5 ∨ (p2 → ((p1 ∧ (p4 ∨ ((p5 → (False → False)) ∧ p1))) ∧ ((p2 ∨ (True → p5)) ∨ (p5 ∧ p1))))) ∨ (False ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157641103447201083699394859778 : (((p1 ∨ (p2 → ((((p3 ∨ ((p5 → p4) ∧ p4)) → p5) ∨ True) ∨ False))) ∧ (p1 → (p3 → p1))) ∨ (p2 ∨ (((p2 → False) → p2) ∧ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260468219477671848238769278140 : ((p3 → False) → ((p5 → ((p3 ∨ ((((p1 ∧ p2) → ((p5 ∨ (p4 → p4)) ∨ (False ∧ p1))) ∧ (p5 ∧ (p4 → p3))) → p2)) ∨ p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152540139538565734588084431879 : ((((p4 ∧ p3) ∨ True) → ((p5 ∨ ((p3 → p3) → (((p4 ∨ True) → p4) → ((p4 ∧ True) ∨ True)))) → p3)) → (p5 ∨ (p3 ∧ (p4 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∧ p3) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p5 ∨ ((p3 → p3) → (((p4 ∨ True) → p4) → ((p4 ∧ True) ∨ True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57294286624633264676111702795 : ((((p2 → p4) → p5) ∨ (p2 ∧ ((((((False ∧ True) ∧ True) → p2) → ((True ∧ p4) ∧ ((p4 → p1) ∧ p4))) → p2) ∨ (p2 ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160832857662351536039756566807 : (((p5 ∧ (p1 ∨ ((True → p2) ∨ p5))) → (((p5 ∧ True) ∨ ((p1 ∨ p3) ∨ (True → True))) ∨ p4)) → (((p5 → p3) ∧ p3) ∨ (False → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327007367305955622122865125328 : (True → (((((p5 ∨ (((False ∨ (p5 ∨ p5)) ∨ (p5 → p4)) ∨ True)) ∧ p1) ∨ (p4 ∨ p3)) ∨ (((p3 ∨ True) → False) ∨ (p3 → p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54171191249227148902521357432 : ((((((False → p2) ∧ (p5 ∧ p1)) → p5) ∧ True) ∧ ((True ∧ False) ∨ (((p2 → (p1 → p5)) ∧ ((p1 ∨ p3) ∨ (p4 → True))) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179216252986627594327907694111 : ((p4 ∧ (((((p1 ∨ False) → p2) → p2) ∨ True) ∧ ((p3 ∧ p2) → False))) ∨ ((True ∨ ((p5 → p4) → ((False ∧ (p4 ∧ p5)) → True))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



