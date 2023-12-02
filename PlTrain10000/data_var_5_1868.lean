variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46783508679811394248850508724 : (((p4 → (((p3 → p3) ∨ ((True → p5) → (p2 → p5))) → (p3 ∨ (((p5 ∧ (p5 ∨ (False ∧ p3))) ∨ p1) ∧ False)))) ∧ (p4 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50984054253545541248276671158 : (((((p1 → p5) → p1) → (((((True ∨ (p1 ∨ p4)) ∧ p4) → p1) → (p4 ∧ p1)) ∨ p3)) ∧ ((((p1 → True) → p5) ∨ p3) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158299448260846498582633969093 : ((((True ∨ p1) → p4) → ((True → False) ∨ (False ∧ (((p2 ∨ (True ∧ True)) → False) → (True ∧ False))))) ∨ ((p4 → True) ∨ ((False ∨ p4) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76773708388444813029689330999 : ((((((False → True) ∨ p3) ∧ ((p2 ∨ p1) ∨ (False ∨ (p2 → (True → p4))))) → ((False ∨ p5) → ((p4 ∨ (p4 ∨ p5)) ∨ True))) → False) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((False → True) ∨ p3) ∧ ((p2 ∨ p1) ∨ (False ∨ (p2 → (True → p4))))) → ((False ∨ p5) → ((p4 ∨ (p4 ∨ p5)) ∨ True))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h3.left
      let h8 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- False on the left can always be used.
            apply False.elim h14
          case inr h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
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
          cases h20
          case inl h21 =>
            -- False on the left can always be used.
            apply False.elim h21
          case inr h22 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h23 := h1 h2
  -- False on the left can always be used.
  apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160200904442081813323407306164 : (((((((p4 ∨ p2) ∧ ((p4 ∧ (p4 → (p3 ∧ p2))) → p2)) ∨ p3) → p1) ∧ p5) ∨ (p1 ∨ False)) → (((p1 → (p4 ∨ p1)) ∧ p1) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307170427433988288920582583625 : (p1 ∨ (False ∨ (p2 → (((False ∧ (p5 ∨ p4)) ∨ (((False → (p2 → (True → p5))) → (False ∧ True)) → (p3 → p2))) ∧ (p2 ∨ (True ∧ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57126986530844261678215079595 : ((((True → p1) ∧ False) ∨ ((((((False ∨ p1) ∧ (True ∧ p3)) ∧ (p5 ∧ p2)) ∨ p2) ∧ ((p3 ∧ (True ∨ p5)) ∧ p4)) → (False ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70490656307029794454416575859 : (((((True → (p2 → (p4 → True))) → (((p2 ∨ p2) ∧ (((p1 ∨ p3) ∧ p3) ∧ (p4 ∧ p3))) ∧ False)) ∧ ((p5 ∧ p4) → p4)) ∧ True) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (True → (p2 → (p4 → True))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h10 := h4 h6
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316624784761154566104737629438 : (p3 ∨ (p4 ∨ ((p2 ∧ ((((p1 → p3) → (False ∨ (False ∧ (p5 → (p3 → False))))) → ((p1 → p2) ∨ p4)) ∨ p5)) ∨ (True ∨ (p5 ∨ p4))))) := by
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
theorem thm_5_vars_721972014236497866718405513243 : ((((True → (p2 ∨ (p5 → p5))) → ((True ∧ (((p4 ∨ False) ∧ (p1 ∧ (((p5 ∧ False) ∧ p3) ∨ p4))) → (p1 ∧ (p5 → True)))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358060083237349819225101039368 : (p5 → (p1 ∨ (((p5 ∨ (p4 ∨ p1)) ∧ (True ∧ p5)) ∧ (((p5 ∧ (((p1 ∨ p1) → p1) ∧ p3)) → (False ∧ (True ∨ (p1 ∨ p3)))) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776522493589870249837870712198 : (((p1 ∨ ((((((p1 → p4) ∧ p5) → p2) ∧ (p3 ∨ p2)) ∧ (p4 ∧ (((True ∧ p2) ∧ ((p3 ∧ p2) ∨ p5)) → (p1 ∧ p1)))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124219998990761063744650073738 : (((((p5 ∧ ((p1 ∧ True) ∧ (p4 ∨ False))) ∧ p4) ∨ True) → ((p5 ∧ (False ∧ p1)) ∨ ((True ∨ p3) → (False ∨ (p3 ∧ p1))))) → (False ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∧ ((p1 ∧ True) ∧ (p4 ∨ False))) ∧ p4) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : (True ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192340114433158852976699685439 : (((p3 ∨ (((p2 ∨ p1) ∧ (p2 ∨ p1)) → True)) ∧ p4) → ((p5 → ((p1 → p2) ∨ (False → (p3 → p1)))) ∨ (p1 ∨ (p4 → (p3 ∨ False))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180212059165930355232144324363 : ((((p4 ∧ p2) ∨ (True ∧ (((True → (False → False)) ∨ p1) ∧ p5))) → p4) → (((p5 → p3) → ((p3 ∨ (False ∧ p5)) ∨ p2)) ∨ (True ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164703830111690599067966525694 : (((((True ∨ p2) ∧ (p3 ∧ ((False ∧ p2) ∧ ((p1 ∨ (False ∧ p3)) ∧ True)))) ∨ True) ∨ p4) ∨ ((((p4 ∧ p1) ∧ p5) ∧ p3) ∧ (p4 ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149401884845748902172733741212 : ((True ∧ (((((p1 ∧ False) ∧ ((((p5 ∧ p1) ∧ p2) → p3) ∨ (p2 → False))) ∧ p4) → (p4 ∧ True)) → p5)) ∨ (((False ∧ False) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50259857107451506027716345992 : ((((False → ((p2 ∧ p1) ∨ (True ∧ (p3 ∨ ((False ∧ (True ∨ p3)) → (p1 → (p4 → False))))))) → p5) ∨ (False → (p1 ∧ (p5 → p4)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789174249285299681677307132363 : (((p5 ∨ ((((p5 ∧ ((p2 → (p1 ∨ (p2 → p4))) ∨ p4)) ∨ p5) → (p1 ∧ (((p3 ∧ p4) → p2) → p5))) → ((p1 → p3) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161925022963593081352893557622 : ((p1 → ((p3 ∨ p1) → (True ∨ ((p1 ∨ ((p5 → p3) → True)) → (((p4 ∧ False) → p3) ∨ p5))))) → ((p2 ∨ (p1 ∨ (p1 → p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592268285178596961075493607430 : ((((((((p2 → (p4 ∨ (p5 → p1))) → (p5 ∧ ((False → (p3 ∧ (p1 ∨ False))) → True))) ∧ (p4 ∨ p2)) → p5) → (p5 → p2)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656774889094158397301036102238 : (((((((p5 ∨ (True ∧ p2)) ∨ p2) ∨ p2) → ((((p3 ∧ p2) ∨ p3) ∨ (p5 → (p4 ∧ (True ∧ (p2 ∨ p1))))) ∧ p1)) ∨ (p4 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191517687465527666921593968595 : ((False ∧ ((p3 → p5) ∧ ((p2 ∨ p1) ∨ (p1 ∨ p1)))) ∨ ((False → ((True ∨ True) → ((p2 ∨ ((True → False) ∨ (p3 → p3))) ∨ False))) ∨ p3)) := by
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
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215099480747902149895428366363 : (((p1 → p1) → (p2 ∨ p1)) ∨ (((p4 ∧ ((p4 ∧ p2) → (False ∨ (p1 → (p5 ∧ (p2 → (p4 → (p1 ∧ (p1 ∧ p2))))))))) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165479527602672386036007120496 : ((((p4 ∧ ((p2 → (p1 → (p1 ∧ p5))) ∨ False)) ∨ p5) ∨ ((p5 ∨ (p5 → True)) → p4)) ∨ (False → (((p5 ∧ (p3 ∨ False)) ∧ False) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h6
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785031725982698775137481565522 : (((p3 ∨ (p5 → (p4 → ((True → (p1 ∨ p2)) ∧ (((p3 ∧ False) ∧ (((p3 → p5) → p2) → ((p1 ∨ (p2 ∧ p4)) ∨ False))) ∨ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698356697830691494790308945517 : (((((p5 ∧ (((p5 ∨ True) ∨ p4) → (True ∨ p5))) ∨ (p5 ∧ False)) ∨ ((((p2 → (p1 → p4)) ∧ (p4 ∧ True)) ∧ (p2 ∧ p4)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_937708410458148504915552835911 : ((((p2 ∧ (p5 ∨ ((False → False) ∨ p4))) ∧ ((p5 → ((p5 ∨ p2) ∧ ((((False ∨ p2) ∧ (False ∨ (p4 → p1))) ∨ True) ∨ p4))) → p5)) → p5) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : (p5 → ((p5 ∨ p2) ∧ ((((False ∨ p2) ∧ (False ∨ (p4 → p1))) ∨ True) ∨ p4))) := by
        -- Implications on the right can always be decomposed.
        intro h10
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h11 := h3 h9
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h13 : (p5 → ((p5 ∨ p2) ∧ ((((False ∨ p2) ∧ (False ∨ (p4 → p1))) ∨ True) ∨ p4))) := by
        -- Implications on the right can always be decomposed.
        intro h14
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h15 := h3 h13
      -- One of the premise coincides with the conclusion.
      exact h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4166330934134219864827780940 : (p4 ∨ (((((True ∧ p2) ∨ (p5 ∨ (p2 → (p1 ∧ p1)))) ∧ p5) ∧ (p1 ∧ p2)) ∨ ((((True ∨ True) ∨ False) ∨ (p1 → p1)) ∨ False))) := by
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
theorem thm_5_vars_187130075790582603310701993782 : (((p1 ∨ p2) ∨ (p1 → ((p4 ∧ True) ∧ (False → (p1 → p1))))) → ((p1 → (((p5 ∨ False) → p2) ∧ p5)) ∨ (p4 → (True → (False ∨ p4))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40498505995873645989343147175 : ((((True ∧ (p4 ∧ (((p5 ∨ p1) ∧ p4) → (p1 ∧ (((p4 ∨ (p4 → p1)) ∧ (p4 ∧ p3)) ∨ ((p5 ∨ p1) → p3)))))) ∨ True) ∨ p4) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234511907580008225120741570039 : ((p2 → (p1 → p4)) → (((p5 ∧ (p2 → ((p2 ∨ p2) → p1))) ∨ p4) → (((p2 → ((True ∨ p5) ∧ (False → False))) ∧ (p4 ∧ True)) → p4))) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691101002222188071886868187377 : (((((((p1 → p3) ∨ (p1 → True)) ∧ (p5 ∧ True)) ∧ (((p3 ∧ True) ∨ p4) ∧ p2)) → (((p4 ∨ (True → (p3 ∧ False))) ∨ False) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9735051806144937912955939645 : ((((True ∧ p4) → ((((p3 ∧ False) ∨ ((p4 ∨ p5) ∨ p1)) ∧ (((p3 ∨ p5) ∧ (p4 ∨ (p2 ∧ (False ∨ False)))) → False)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215037940149741364770507660813 : (((p2 ∨ p4) → (False ∨ p2)) ∨ ((((((p4 → ((p2 → True) ∨ (p5 → False))) ∨ p5) → p5) → p2) ∨ (p3 → p2)) → (p3 ∨ (p3 ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684764823380918081989461236081 : (((((p4 ∧ False) ∨ ((p4 ∨ ((p1 ∧ True) → p4)) → ((((p2 ∨ p5) ∨ False) → p2) → False))) ∨ ((False → ((p2 → p5) ∨ p1)) → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229456678548478443246917642518 : ((p1 → (p5 → p4)) ∨ ((((((p1 → p3) → True) ∨ p3) → ((False ∨ p2) ∨ p1)) ∨ p2) ∨ (((((p1 ∧ p5) → p4) → p2) → p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762272880094787896398570065416 : (((p3 ∧ ((p1 ∨ (p1 ∨ (((((((p3 → (p1 → p4)) ∨ p1) ∨ p1) ∧ (p4 ∧ (False ∧ True))) → p4) ∧ p5) ∨ p2))) → (p5 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324487960321868065229772268486 : (p5 ∨ ((((p2 ∨ p5) → p2) → False) ∨ (((False ∧ (p2 ∨ ((((p5 ∨ p5) ∨ False) → (p4 ∨ (p1 → p4))) ∨ True))) → p5) ∧ (True ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147706822884511118948943860609 : ((((((p3 ∧ (((p2 ∨ p4) → p5) → True)) → p4) ∧ p1) ∨ ((((p2 → True) → p4) → p3) → p4)) → p3) ∨ (p2 ∨ ((True ∨ p2) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161019606996896938363942368766 : (((p3 ∨ (p5 → p4)) ∨ ((p3 → True) → ((((p3 ∧ (p3 ∧ p4)) ∧ (p4 → p5)) ∧ p4) ∧ p5))) → ((p3 ∨ (True → (p5 ∧ p2))) ∨ True)) := by
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
theorem thm_5_vars_742792655334507014558440840826 : ((((p3 → p1) ∨ ((p5 ∨ (p1 ∧ (((p2 ∧ (p4 ∨ (((True ∨ (p1 ∨ p4)) → p1) ∨ p4))) ∧ ((p1 ∨ False) → p5)) ∧ p5))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324229070710584683295412769760 : (p5 ∨ ((((p3 ∨ (p3 ∨ True)) ∨ p5) ∨ (p5 → p5)) ∧ (True → ((False ∧ (p4 ∨ p3)) ∨ (True ∨ ((p2 ∧ p1) → (p2 ∨ (p1 ∧ p2)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767529237166567521686280496858 : (((p5 ∧ (((p2 → (((((p3 ∨ (((False → (p2 ∧ p5)) ∧ p3) ∨ p4)) → p3) ∧ (p4 ∧ (p4 ∨ p3))) → p5) ∧ True)) → p3) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305600750776016839936489469276 : (p1 ∨ ((p2 ∨ ((p5 → False) ∧ ((p1 ∨ (p1 ∨ (p1 ∨ p2))) ∧ p5))) ∨ (((((((True ∧ p1) ∧ False) → p1) ∧ p4) ∨ p3) ∨ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_920793703651713636851582582106 : (((((p2 → ((False ∧ p4) ∨ p2)) → ((p3 ∧ p4) ∧ ((True ∧ p2) ∧ True))) ∨ (p4 ∧ (p5 ∧ ((((p4 ∧ p4) ∧ False) ∧ p4) ∧ p3)))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (p2 → ((False ∧ p4) ∨ p2)) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h3
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h18.left
    let h21 := h18.right
    -- False on the left can always be used.
    apply False.elim h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48464522534388703101178578913 : (((((p3 ∧ (p4 → ((False ∧ ((p2 ∧ p3) → (p1 → False))) ∧ (False ∧ ((p3 ∧ p2) ∨ False))))) → p1) ∧ p2) ∧ (p5 → (p5 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62693300293204992382315094212 : ((p4 ∧ ((((p1 → ((p5 ∧ p2) ∨ ((p1 ∧ (p3 ∨ p2)) ∨ (p2 → p2)))) ∨ (True ∨ (p5 → ((p5 ∨ True) → p1)))) → True) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159058039763094743594649060918 : ((p5 ∨ (((((p5 → p4) → p4) ∨ p4) ∧ (p5 → p5)) → ((((p3 ∧ True) ∨ p3) ∨ True) ∨ p1))) ∨ (False ∧ ((p2 ∨ p1) → (p4 → False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44683934532013422728327027993 : ((((p3 ∧ (p3 ∨ (p3 ∨ (False ∨ p3)))) → (p2 ∨ (((p5 → ((p5 ∨ ((True ∨ p1) ∧ (False ∧ False))) ∧ p1)) ∧ p2) → False))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761882298299867901925165151601 : (((p3 ∧ (((((((p1 ∨ ((p2 ∨ (True → True)) ∨ p1)) → True) ∧ p1) ∨ True) → (True ∧ (p3 ∨ p5))) ∨ ((p4 ∧ True) ∨ p3)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53806564549199254847345974459 : ((((p1 ∨ ((p4 ∨ False) ∨ ((p3 → p1) ∨ p2))) → p2) ∨ (((p5 → True) ∨ p4) → ((p5 → ((p5 → p5) → (p2 ∧ False))) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731278397615110016706238240218 : ((((p4 ∨ (p1 ∧ False)) → (((p3 ∧ p4) ∧ (p3 → (p3 ∧ (p2 → ((p5 ∧ (((p2 ∧ p3) ∨ (p2 ∧ p1)) → p5)) ∨ p1))))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699118179039747675514718834513 : ((((p5 ∨ (p2 → ((p4 ∨ (p1 → p3)) ∨ ((p1 ∧ False) ∧ p2)))) ∨ ((p5 → (((p5 → True) ∨ p5) ∧ (p5 → (p3 ∨ p4)))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68786588802802823717759967378 : ((p4 → (((p2 → (p3 ∧ p1)) ∨ ((p5 ∨ p2) → p3)) → (p2 ∧ (False → ((p1 → (p4 → (((p1 ∧ p5) → False) ∨ True))) ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50633895237174893043802428327 : (((((((p2 ∧ p4) → p3) ∨ (False ∨ p2)) ∨ ((p5 ∧ False) ∧ p5)) ∧ ((True ∨ p4) → (p3 ∨ True))) → (p4 ∨ (p2 ∧ (True → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775680261266860533089876669194 : (((False ∨ (p2 ∨ (((((p2 → (p1 ∨ (((p4 ∨ (p1 ∨ (p1 ∨ p2))) ∧ p3) ∧ (False → (p2 ∨ p2))))) ∨ True) ∧ p4) → p2) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58599530603896825433257389176 : (((False → False) ∧ ((p4 → (p3 ∨ (p5 → p2))) ∨ (((((p4 ∧ p4) → (p4 → (False ∨ p4))) ∨ (p4 ∧ p4)) ∨ (p4 → False)) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260819737323075995126830373144 : ((p3 → p5) → (p3 → (True → (((p5 → ((False ∧ p3) ∨ False)) ∨ p4) ∨ ((((p2 → ((p3 ∧ p2) ∨ (p5 → p1))) ∧ True) ∧ True) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244946585930253879478855814531 : ((p1 ∧ p3) ∨ ((p3 ∨ ((True ∧ p2) → p1)) → ((((p4 ∨ p4) ∧ (((True → p3) ∧ (p3 ∨ (p4 ∨ p5))) ∨ p4)) → (p5 ∨ True)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h13 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h20 =>
          -- Disjunctions on the left can always be decomposed.
          cases h20
          case inl h21 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h22 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h22
      case inr h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h24 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h25
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h29 =>
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h32 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h33 =>
          -- Disjunctions on the left can always be decomposed.
          cases h33
          case inl h34 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h35 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h35
      case inr h36 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h37 =>
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h38 =>
        -- Conjunctions on the left can always be decomposed.
        let h39 := h38.left
        let h40 := h38.right
        -- Disjunctions on the left can always be decomposed.
        cases h40
        case inl h41 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h42 =>
          -- Disjunctions on the left can always be decomposed.
          cases h42
          case inl h43 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h44 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h44
      case inr h45 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616463456776978481064415715680 : ((((((p1 ∨ (p2 ∨ p5)) ∧ ((p5 → (p1 → (True ∧ p4))) → p5)) → (p5 ∨ (p4 ∨ ((((p1 ∨ p5) ∧ p5) → p4) ∨ False)))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_346685325224015374232993910056 : (p3 → ((((p1 ∨ (p4 ∧ p4)) → False) ∧ ((p1 ∧ p5) ∧ (p1 ∨ (((((p2 → p4) → False) ∧ False) → False) ∨ p4)))) → (p4 ∧ (p1 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h9 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : (p1 ∨ (p4 ∧ p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h14 : (p1 ∨ (p4 ∧ p4)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h15 := h3 h14
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h16
  -- Implications on the right can always be decomposed.
  intro h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201094248590693059522102868644 : ((True → (((False ∧ (True → p2)) → p1) ∧ False)) → (((p5 ∧ (((p5 ∨ p1) ∧ (True ∨ p4)) ∧ p4)) ∨ False) ∧ ((p3 → (p5 ∧ True)) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345520612828771612671098697915 : (p3 → (((p1 ∨ ((((p2 → (True ∨ (p4 → p3))) ∧ p2) ∧ False) ∧ p5)) ∨ (p1 → (p5 → ((p3 → False) ∨ (p1 ∨ (False ∨ p2)))))) ∨ p2)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678933833842826382558512519745 : ((((p3 ∧ (p2 → ((True → ((True → (((True ∨ True) ∨ (p2 ∧ p5)) → p4)) ∨ (p3 ∨ p5))) → p5))) ∨ ((p5 ∧ (False ∧ True)) → True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_54326483127741299141167830168 : (((p2 ∧ ((p4 ∨ ((p4 ∨ p2) → p3)) ∧ p1)) ∧ (((p2 → True) → ((True → True) → (((p1 ∧ p1) → p2) → p5))) → (p5 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137766489903855557600252309220 : ((p2 ∨ (((((False ∨ p3) ∧ (((p4 → p4) ∨ p5) ∨ p5)) ∧ (True → p3)) ∧ (p2 ∨ p5)) ∧ ((p1 ∨ p4) ∧ True))) ∨ (True ∧ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182618950250106193813699559310 : ((((True → p2) ∧ ((p3 ∧ p3) ∧ p3)) ∨ ((False ∧ False) ∨ True)) ∧ ((p4 ∧ False) → ((p1 ∧ p4) ∧ (p3 ∨ (p4 ∨ (p5 ∨ (True → p5))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42250664390679348601531884878 : (((p1 ∧ ((((p5 → True) → ((p4 ∧ p4) ∧ (((False ∨ False) → (False → False)) → (False → (p4 ∨ p1))))) ∧ (p3 ∧ p1)) ∧ p3)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608914913505799543431109931841 : (((((((p3 ∧ p4) ∧ (((True ∧ (p2 ∧ (p1 ∨ False))) ∧ p1) ∧ (False ∧ False))) ∨ ((p3 ∨ ((p3 → True) ∧ p4)) ∧ p1)) ∨ False) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58874293598511427201479045642 : (((False ∧ False) ∨ (((True ∧ (p5 → ((p4 ∨ (p5 ∨ p1)) ∧ (p4 ∧ (True → p1))))) ∨ p2) ∨ ((p4 ∨ (True ∨ (True → p4))) ∨ p2))) ∨ False) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_901464074218719476984101601186 : (((((((p4 → True) ∨ ((p2 ∧ (True ∧ (((p1 → True) → p2) → p4))) ∨ p3)) → (False ∧ p3)) ∧ p1) ∧ (p2 → ((p3 → p4) ∧ False))) → False) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((p4 → True) ∨ ((p2 ∧ (True ∧ (((p1 → True) → p2) → p4))) ∨ p3)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199130544105794457726675283857 : ((((True ∧ True) ∧ (p1 → (False ∨ p3))) ∧ p4) → (p5 → (p5 ∧ ((((p4 ∨ p2) ∨ True) → p1) → ((p3 ∨ (p3 ∨ p1)) ∨ (p1 ∧ True)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h16 : ((p4 ∨ p2) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h17 := h9 h16
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164849774636127584914286742009 : (((p5 ∧ (p5 ∧ (((p4 ∨ p4) ∧ p1) ∨ ((True → False) → ((p3 ∨ p2) ∧ p4))))) ∨ p2) ∨ (p1 ∨ (True ∧ (((False ∧ False) → p5) → True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732629708027949613107608689979 : ((((p1 ∧ p1) ∧ (p4 ∨ (p1 ∨ (((((p3 → True) → p5) → p3) ∧ True) → ((((p3 → p3) ∧ p1) ∧ False) ∧ ((p1 → p2) → p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56769022820513554150086473084 : ((((True ∧ p5) → True) ∧ (p5 ∨ ((False → p1) → (((((p5 → (p3 → p4)) → False) → p5) → (p2 ∨ (p2 ∧ (p1 → p1)))) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300721816711131872242255579517 : (False ∨ ((((p2 → True) ∨ p5) → ((((p4 ∨ ((p2 ∧ False) ∧ p5)) ∨ (p3 ∧ p4)) → True) ∧ p3)) → (((p1 → p4) ∨ False) ∨ (p5 ∨ True)))) := by
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
theorem thm_5_vars_165247543922671546324940903067 : (((p4 ∨ ((p3 → ((p5 → ((p4 → (p3 ∧ p1)) ∨ False)) ∨ p5)) → p4)) ∨ (p4 → False)) ∨ (((p2 → ((True ∧ True) ∨ True)) ∨ p3) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_204905236547001114940228090389 : ((((p3 → True) ∧ (p3 ∨ False)) → p1) ∨ (((((((True ∨ p2) → p3) → (False ∧ p1)) → p1) ∨ p3) ∨ p4) ∨ (p5 ∨ ((p1 ∧ False) → p4)))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141768628560304944051369853022 : (((p4 → p1) ∧ (((p3 ∨ True) → ((p4 ∨ False) → p5)) → (((p3 → p4) ∧ (p5 ∧ p2)) ∧ (p3 → (p5 ∧ p2))))) → ((p1 ∨ p3) ∨ True)) := by
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
theorem thm_5_vars_322240099956772307418800503748 : (p5 ∨ (((((((True ∧ p5) ∨ (((p2 ∨ (p2 ∧ (p1 → p5))) → p5) ∨ ((p2 ∧ (p4 ∨ p4)) ∧ p3))) ∧ True) → False) ∨ p2) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177987622835191784688366095733 : (((p4 ∧ ((p5 ∨ ((p3 → p4) ∨ False)) → ((p2 → False) ∧ False))) ∨ True) ∨ (((p2 ∧ ((p4 → p2) → ((p5 ∧ p5) → p5))) ∧ p4) ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139188098157444741703064438004 : ((((False ∧ (((False ∨ True) ∨ p4) ∨ False)) → ((p1 ∧ (p4 → ((False → (False → p3)) → True))) ∨ (p5 ∨ True))) ∨ p1) → (p3 → (p5 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249969288191994446590904949035 : ((True → p2) ∨ ((((((p2 → False) ∧ p3) ∨ (((p5 → p1) ∨ (((p4 ∨ True) → p5) → p2)) ∨ p5)) ∧ (p5 ∧ p1)) ∧ p1) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664360047804118770623574496336 : ((((p2 ∨ (p3 → (((((p5 ∧ (p5 → False)) ∧ False) ∨ ((p1 → p5) → (p3 ∨ p4))) ∧ (p5 ∧ p3)) ∧ (p4 ∨ p5)))) → (p2 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49324213976096225781014237774 : (((p4 ∨ ((((True ∨ p2) ∨ (p1 → True)) ∧ (p1 ∧ ((p2 → (p5 → False)) ∨ (True ∨ (p4 ∨ p2))))) → p2)) ∨ ((p2 ∨ True) ∧ True)) ∨ p5) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651072697363953416895988835218 : (((((False ∧ (False ∧ (False ∧ p2))) ∧ (p3 ∧ ((p4 ∨ (((p1 ∨ (p2 ∧ p2)) ∨ (p4 ∧ (True → p4))) ∨ True)) → p2))) ∧ (p3 → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56915948951673765518124822290 : (((p5 ∧ (p5 ∨ True)) ∧ (((p4 → p1) ∧ (True ∧ p2)) ∨ ((((((((True ∧ p3) ∨ True) ∨ p4) ∨ p5) → True) ∧ p4) → False) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729692029876570363188696975809 : (((((p1 → p3) ∨ p1) → (((((True → p1) ∨ (((False ∧ p1) → p3) ∧ ((p4 → p2) ∨ False))) → p1) ∨ p1) → (p2 → (p5 ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197369759057644765762182927782 : (((True ∨ ((p2 ∨ False) ∨ (p1 → p4))) → False) ∨ (p3 → (((p5 → p5) → (((p1 ∧ True) ∧ False) ∧ False)) ∨ (p4 ∨ (p4 ∨ (p2 ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329535024337836023185583044941 : (True → ((p4 ∧ False) ∨ ((p3 ∧ ((((p3 ∨ (p3 ∨ False)) → (False ∨ (p1 ∨ True))) ∧ p4) ∧ (p3 ∧ ((p3 → False) ∨ p1)))) ∨ (p2 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178073337266446712420363687859 : ((((p4 ∨ (((p2 → p4) ∨ (False ∧ (p4 ∨ False))) ∨ True)) ∨ False) → p4) ∨ ((p3 ∨ p1) ∨ ((p5 ∧ (p4 ∧ True)) → (False ∨ (p4 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214472684071070856475026500536 : (((False ∧ p2) ∧ (False ∨ False)) ∨ ((p1 → (True → ((p4 ∨ p2) ∧ (p2 ∧ p5)))) ∨ (True → (((((False ∨ p2) ∧ True) ∧ p2) → True) ∨ p3)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318385801925835486174566831817 : (p4 ∨ ((True → (((p4 → (((p2 → p2) → (True ∨ (p1 → p2))) ∧ True)) ∨ (True → (((p1 ∧ p2) ∨ p3) → p2))) ∧ (p3 ∧ False))) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153710809777022101144087955115 : ((p3 → ((((p1 ∧ ((False ∨ p1) ∧ p5)) ∨ p3) ∧ (((p1 ∧ (p3 → (p5 → p3))) ∨ True) ∨ p1)) ∨ True)) → (((True → False) ∧ p3) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141650723124085619166798740521 : (((True ∧ p2) ∧ ((((p1 ∨ (p3 ∨ p5)) ∨ True) ∨ (p1 → (p1 ∨ (((True ∨ p2) → p1) → (p5 → p3))))) ∧ p3)) → (p4 ∨ (p1 ∨ p2))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173392625414386955051518046738 : ((p4 → ((p1 ∨ (True → p1)) → (p2 ∨ (((True ∨ (p5 ∧ False)) ∨ False) → False)))) ∨ (False ∨ (((p4 ∧ (p5 → p4)) ∨ (False ∨ p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342752984037749097466732599978 : (p2 → (((p2 ∧ ((p5 → True) → p5)) ∧ (p4 ∧ True)) ∨ (p4 ∨ (p5 → (p5 → (((p4 → p4) ∧ p2) ∨ ((p4 ∨ (p5 → p3)) ∧ p1))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632978271119442031748151247396 : (((((((((True ∨ p3) ∨ p4) ∨ ((p1 ∧ (p1 ∧ p3)) ∨ True)) → True) ∨ (((True → p4) ∨ (p5 ∨ p3)) ∧ True)) ∧ (p1 → p3)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311293180142950410271232450443 : (p2 ∨ (True ∧ ((True → False) → (False ∨ (True → (True ∧ ((((p5 ∨ False) ∧ (((p2 ∨ p1) ∨ p3) ∧ (p2 ∨ (p2 → p1)))) ∧ p5) → p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



