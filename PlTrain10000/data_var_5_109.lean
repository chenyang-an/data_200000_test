variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160296468703413129890396854505 : ((((p5 ∨ (((p2 ∧ p2) → (False → (False → ((True ∧ p1) ∧ p3)))) ∧ p1)) → p1) → (False ∧ p5)) → ((p4 ∨ (p2 → (True → p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49334493239937514867382819619 : (((p5 ∨ (p5 ∨ ((p2 ∧ (p3 ∧ ((p5 ∨ (p4 → ((p2 ∨ p2) ∧ p2))) → (p4 ∨ (p4 ∧ True))))) ∧ p1))) ∨ ((p4 → p4) ∨ False)) ∨ False) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343371876304956163631488953546 : (p2 → ((p5 → p2) ∧ ((((p5 ∨ (p2 ∧ (((((p5 → p5) → p4) ∨ (False → p1)) ∨ p2) ∨ False))) → p2) → ((p4 → p2) ∧ False)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156714723563487871911043881271 : ((((((p4 ∧ True) ∨ p4) → (p3 → (p3 ∨ p3))) ∧ ((p1 ∨ ((p4 ∧ p2) ∧ True)) ∨ False)) ∧ p1) ∨ (((False ∧ p4) ∧ p5) → (True → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610823336995301191892799495897 : ((((((((p3 ∨ p2) ∧ (((p1 → p1) ∨ p2) ∧ p5)) → ((p1 → p3) ∧ False)) ∧ ((p3 → (True → (p2 ∨ False))) ∧ p4)) → p2) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304857081099593600067580294617 : (p1 ∨ (((((False ∧ p1) → p2) ∧ p5) ∧ (p5 ∧ (p2 ∧ ((p1 ∨ ((((p2 ∧ True) ∧ False) → (p3 ∧ p5)) ∨ p2)) ∨ p4)))) → (p3 ∨ True))) := by
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
  let h6 := h3.left
  let h7 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
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
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324168189801652110434754577210 : (p5 ∨ (((p5 ∨ (p4 ∨ (p2 ∨ (False ∨ p2)))) ∨ (p1 → False)) ∨ ((((((p4 → p4) → (True ∨ p2)) ∧ False) → True) → (True ∨ p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58214868523146218068311455322 : (((p4 ∧ p2) ∧ ((p5 ∨ (((True ∨ (p3 → True)) ∧ (p5 ∨ (p1 ∧ False))) ∨ (((p1 ∨ False) → p4) → (p4 ∨ (p3 → p1))))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49264675102059491716154138570 : (((p1 ∧ ((p4 → False) ∨ (((p4 → (p5 → False)) → p4) ∧ (((True → (p2 → p2)) ∧ (p4 ∧ p3)) ∧ p1)))) ∨ (p5 → (p1 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_875456353711665817877459252922 : (((((((p4 ∨ (p3 ∧ ((p4 → ((False ∨ (p1 ∨ False)) ∨ (False ∨ p4))) → False))) ∨ (p3 → (True ∨ p5))) ∨ False) → p4) ∧ (p4 ∨ True)) → p4) ∧ True) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : (((p4 ∨ (p3 ∧ ((p4 → ((False ∨ (p1 ∨ False)) ∨ (False ∨ p4))) → False))) ∨ (p3 → (True ∨ p5))) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h6
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644394744403325491234248175257 : ((((False ∨ (True ∧ ((True → p3) ∨ (((True → (p2 ∧ (True ∧ p5))) → p3) → ((((p3 ∨ p5) ∨ p5) ∨ False) → (p4 ∨ False)))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160233587558040025255050704349 : (((((((p3 → p1) ∨ (p1 ∨ False)) ∧ p5) ∨ p5) ∨ ((True ∧ p3) ∧ (p4 → p5))) ∨ (True ∧ p3)) → ((((p5 ∨ p1) → p3) ∨ True) ∨ False)) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h7 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
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
            -- False on the left can always be used.
            apply False.elim h10
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134557427413661240947350309141 : ((((p4 ∧ ((p2 ∧ (False ∧ p2)) ∧ (((p5 ∨ (True → p3)) ∧ False) → ((p2 ∧ p4) ∧ (p5 ∧ p2))))) → p3) → p5) ∨ (p4 ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114324604607335344296687018027 : ((((False ∨ p2) ∨ ((p2 ∨ p1) ∨ ((p1 → True) → ((p1 ∧ (p2 ∧ (p3 → p5))) → p3)))) ∧ (p5 ∨ (False ∨ (p5 → True)))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617638699918606735992165127445 : (((((((p4 ∧ (False ∧ p4)) ∧ p4) ∨ p5) ∨ (((False ∧ (p5 → p2)) ∨ (True ∨ p3)) ∨ (((p1 → False) ∧ p1) ∧ (p1 ∧ p5)))) ∨ p1) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55195014764180609302622268848 : ((((p3 ∨ (True ∨ (p2 → p3))) → False) ∨ ((p2 ∧ p5) ∨ (((True ∨ (p2 ∨ p1)) ∧ ((p3 ∧ (True ∨ (p3 ∨ True))) → p1)) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265572453892226536271501938975 : (True ∧ (p1 ∨ (((False ∧ (((False ∨ ((((p2 → False) → True) → (p2 ∧ p2)) ∧ p2)) ∧ (True ∧ True)) ∧ (p3 → (p3 ∨ True)))) ∨ p3) ∨ True))) := by
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
theorem thm_5_vars_149952497819257917827723690351 : ((p4 ∨ (((p2 → (p1 → (((p5 ∨ p3) ∨ ((p2 → (True ∧ p4)) → p4)) → (False ∧ False)))) ∧ True) ∧ p2)) ∨ ((p4 ∧ True) → (p5 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210397473822557468086828184857 : (((p1 ∨ (False → False)) ∨ p5) ∧ (((True ∧ (p3 ∨ (False ∧ p3))) ∧ (True → (((p2 ∨ p4) → ((p3 ∨ p5) ∧ p3)) ∨ False))) ∨ (True ∧ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50746505634208539429268369760 : (((p2 ∧ (p2 ∨ ((((p4 ∨ True) → (p3 ∧ False)) ∨ (p4 → (p3 ∨ (p2 → p1)))) ∨ (False ∨ p1)))) → ((p4 ∧ (p1 ∧ True)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64004590883844219029297662807 : ((False ∨ (((((True → p5) → False) ∧ (False ∧ (p2 ∨ p5))) ∨ ((p5 ∧ ((p5 ∨ p2) ∨ p5)) ∧ ((p3 ∨ p3) ∨ p4))) ∧ (p5 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645926974698267777380229462959 : ((((True → (((False ∨ (((p5 → p1) ∧ p5) → ((True → (p1 ∨ (p5 ∨ p1))) ∧ p1))) ∧ ((p1 → p2) ∧ p4)) ∧ (False ∧ p1))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227480664283510001765698478814 : ((True ∧ (p4 ∧ p1)) ∨ (((True ∧ False) ∧ p3) ∨ ((False ∨ p5) ∨ ((p2 → ((p4 → (p1 ∨ ((False ∨ True) ∨ p1))) → p2)) ∨ (p4 ∧ p2))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58748332509877959916746214254 : (((p4 → True) ∧ ((((((p1 ∨ True) ∧ p1) ∨ p5) → (p5 → p3)) ∧ (p2 ∧ ((p5 → p4) ∧ ((p3 → p4) ∨ (p2 → p4))))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172428405492292211129045019880 : (((p4 ∧ (p3 ∧ (True → False))) ∧ (p3 ∨ ((((p3 ∧ p2) → p3) ∧ p4) ∨ p3))) ∨ ((((p4 → p5) ∨ True) ∨ (True ∨ (p1 → p1))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303744701786844179693674074616 : (p1 ∨ (((((((((p5 ∧ False) ∨ p5) → (p2 ∧ True)) → ((p2 ∨ False) ∧ p3)) → ((p2 → p4) ∨ False)) ∨ (True ∧ p4)) ∧ p3) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229561110929916347663482905902 : ((p2 → (p3 → p1)) ∨ (((False → p1) ∧ ((p2 ∧ (p5 ∨ p5)) ∨ (p4 → (True → p2)))) ∨ (False ∨ (p4 ∨ (p1 ∨ (p1 → (True ∨ p5))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124750864215022589689777646986 : ((((p4 ∨ p4) ∨ (True → p5)) ∧ ((False → ((p4 ∨ ((p1 ∧ (p3 ∨ p4)) ∧ (p2 ∨ p1))) → (False ∧ p5))) ∨ (p1 ∧ False))) → (p4 ∨ p5)) := by
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
      cases h3
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- False on the left can always be used.
        apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h18 := h15 h17
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- False on the left can always be used.
      apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339876195697007373272253752943 : (p1 → (True → ((p2 ∧ (p5 ∧ True)) ∨ (((p2 → ((p5 ∨ False) → p1)) ∧ p5) → (((((True ∧ p5) → p1) → p3) ∨ p1) ∧ (p3 → p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h3.left
  let h8 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177880231364828069082484425897 : (((((p2 → (((True → False) → p2) ∨ p1)) → (p5 → p2)) → p1) ∨ p1) ∨ (((((False ∧ (True ∨ p2)) ∧ False) ∧ p2) → (True → p2)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300098611178953370151458856892 : (False ∨ ((((((False ∨ False) → (p3 ∨ (((p5 ∧ p4) → p1) → (p5 → p1)))) → False) ∨ p4) ∨ (((False → p1) ∨ True) → p4)) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664324657945847690394560402438 : ((((p2 ∨ (((True ∧ True) ∧ (p3 ∨ (p4 ∨ (True ∨ p1)))) ∧ ((((p4 ∧ p2) → p1) → p1) → ((p1 ∧ p4) ∨ True)))) → (p1 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_946987036973220634903395556365 : (((((p5 ∧ (p3 ∧ p2)) ∨ True) → (((((p2 ∧ (p3 ∧ p1)) → ((((p4 ∨ p2) ∧ True) → p5) → (p3 ∨ p1))) → p5) ∨ p1) ∧ False)) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∧ (p3 ∧ p2)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725207469767345167221545757943 : ((((p2 → (False ∨ p3)) ∧ (((p3 → ((True ∨ p1) ∨ (False ∨ p5))) ∨ False) → ((p5 ∨ ((p4 ∨ p4) ∧ p5)) → (p3 ∨ (True ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109883685260555085154541054558 : ((True → (((((((p1 → p1) ∨ False) ∧ (p3 ∨ ((((p4 → p3) ∧ p4) ∨ True) → p3))) ∨ p3) ∧ p2) ∨ (p4 → p4)) ∨ p2)) ∧ (True ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112343041471087742882028749539 : (((p5 → ((((p5 → (p3 → (((p3 ∨ p3) ∧ p4) → p4))) → p4) ∨ p2) ∨ (((p1 ∨ (True → p2)) ∧ p4) ∧ False))) ∨ p2) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112067221791805108928835074975 : ((((True → p2) ∧ ((p2 → (p4 → ((((p2 ∧ p1) ∨ p4) → (True ∧ False)) ∨ (p4 → (False ∨ False))))) → (p5 ∧ False))) ∨ p1) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60489503655386614747528065238 : ((True ∧ (((((True ∧ p1) ∧ p4) ∧ ((p2 ∨ ((False ∨ p3) → ((((True ∨ p3) → p4) ∨ False) → p2))) → (True ∧ True))) → p3) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668005758237658023330725566870 : ((((p4 ∨ (((p2 → (p2 ∨ False)) → (p1 ∨ True)) → ((p3 ∨ (p1 ∧ ((p1 → p5) → p1))) ∧ (True ∧ p2)))) ∧ ((p5 → p5) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702804475203850370969765839363 : (((((((p1 ∧ p4) ∨ p2) → False) ∧ (True ∧ (p2 ∨ p4))) ∨ ((False ∨ (p1 ∨ p3)) ∨ ((p3 ∨ (((p2 ∧ p2) → p3) → True)) ∨ True))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67517801273941751773434024330 : ((p1 → (((False ∧ (False ∨ False)) ∧ (p2 → False)) ∨ (((p2 → (p2 → p2)) ∧ p5) → (((p4 → (False ∨ p2)) ∨ (p2 ∧ p5)) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60219715142156733968666050658 : (((True → p1) → ((False → p5) → (((p5 → p3) → False) → (((((True ∧ False) ∧ p3) → p4) ∨ p2) → (p3 ∧ ((p3 ∨ p5) ∨ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591664401498618569380959998571 : ((((((((p4 ∨ (False ∨ ((p5 ∧ p4) ∨ (p1 → p5)))) ∨ ((True ∨ (True → (True ∧ p5))) → p3)) ∧ p5) ∨ True) ∨ (False → p3)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171525334463502047631823925974 : (((((p1 → (p2 ∨ (((p4 ∧ p1) ∧ (False ∨ p5)) ∨ p1))) ∧ p4) ∨ True) ∨ False) ∨ ((True ∧ (((True → p5) → p5) ∨ True)) ∧ (p4 ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55704208933231675908650491254 : ((((False ∨ (p1 ∧ p2)) ∨ p1) ∧ ((p3 → ((p3 → (p4 ∧ (True ∧ ((False ∨ p1) ∧ p2)))) → (p2 → p5))) → ((p5 ∧ True) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167888260270249327561539655221 : (((p1 → (p1 ∨ (((p5 → (p4 → p1)) ∧ p2) ∨ True))) → ((p5 ∨ (p4 → False)) ∧ False)) → (((p3 ∧ (p3 ∧ (p3 → p2))) ∨ p1) → p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h11 : (p1 → (p1 ∨ (((p5 → (p4 → p1)) ∧ p2) ∨ True))) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h13 := h1 h11
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323269358318825680593961827171 : (p5 ∨ ((p4 ∨ (((False ∧ (p1 → (p2 → (p2 ∧ False)))) → p1) ∧ ((((p3 ∧ p2) ∨ p3) ∨ (p4 → p1)) ∨ (p4 ∧ p4)))) ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165270211559049610786713231687 : (((((((p4 ∨ (True ∨ p4)) → False) ∨ ((p3 → p3) → p3)) ∨ p2) → False) → (p3 ∧ p4)) ∨ (((p1 ∧ p4) → ((False ∨ p2) ∨ p1)) ∨ p3)) := by
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
theorem thm_5_vars_56260633550113676324234248592 : (((p2 → ((False ∧ True) ∨ False)) ∨ ((((p4 → ((False ∧ (p5 ∨ True)) → (p4 ∨ (p1 ∨ p5)))) ∧ (p4 ∧ p1)) → (p3 ∧ True)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41614904575889740037764943750 : ((((True → (p5 ∧ (True ∧ ((p2 ∨ p1) ∨ p2)))) ∨ (((((p1 ∧ p3) ∧ True) ∨ p5) ∧ (p1 ∧ p3)) ∨ ((p2 ∧ p4) → p2))) ∨ p1) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312305174187918537536900308429 : (p2 ∨ (p2 → ((((p1 ∧ (p1 → False)) ∧ (False ∧ p2)) ∧ ((p1 ∧ (p1 ∧ (p5 ∨ ((p2 ∧ p1) ∨ False)))) ∧ False)) ∨ ((p5 ∧ False) → p4)))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153630037075734146711546894313 : ((p1 → ((False ∨ (p3 ∧ ((p1 ∧ ((((True ∨ True) ∧ False) ∧ p3) → p3)) → p4))) → ((p2 → p4) → False))) → (((p1 → p1) → p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134851541623285791282428625052 : (((p5 ∨ ((True ∧ ((((p2 ∨ p2) ∧ p3) ∧ (p5 ∧ p1)) → (p3 ∧ p2))) ∨ ((p4 ∧ (p5 → p4)) ∧ p2))) → p3) ∨ ((False ∨ False) → p2)) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_443503425259896460533586783047 : ((((((p5 ∨ (p3 ∨ (True ∧ (p4 ∧ False)))) → p1) ∨ ((p4 ∧ (p2 → p3)) ∧ (((p1 ∨ p3) ∧ False) ∨ p3))) ∨ ((p1 ∨ True) ∨ p1)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_149026392094000527591711340001 : ((((p4 ∨ p3) → p4) ∨ (((((p4 → ((False → p4) ∨ True)) ∧ p5) ∧ (p4 ∧ (p1 ∧ p2))) ∧ p2) ∨ True)) ∨ ((True ∨ (p4 → True)) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677470542403474476661208803767 : (((((((p1 → p5) ∨ ((False ∨ False) ∨ (p5 → p2))) → ((p3 ∧ ((p1 ∧ p1) → p4)) ∧ False)) ∨ p5) ∨ (p3 → (True → (True → True)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90378420377981625230702292630 : (((True ∧ p2) ∧ ((((((p3 → p5) ∧ p2) ∧ p5) ∧ (((p1 ∧ p1) → p5) ∧ (((False ∨ p1) ∧ (False ∧ False)) → p4))) ∧ True) ∧ p3)) → p5) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h11.left
  let h17 := h11.right
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340957291703463298035046829771 : (p2 → ((((p5 → p3) ∧ p5) → ((((p5 → True) → ((p3 → (False ∧ (p4 ∧ (False ∧ (p4 ∨ False))))) ∨ True)) ∧ (p2 ∧ p3)) ∨ False)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256050680703698102079445737658 : ((True ∨ p4) → ((((p1 ∧ ((p2 ∨ p2) ∨ p5)) ∨ (True → p2)) ∧ (False ∧ ((False → p5) → p4))) ∨ (True ∨ ((True → (p3 ∧ p5)) ∧ p4)))) := by
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
theorem thm_5_vars_156756986572154460641447226754 : ((((p4 ∧ p1) ∧ (((False ∧ (p4 ∨ False)) ∨ (p1 → p1)) ∨ (False ∧ (p2 → (p2 ∧ p5))))) ∧ p2) ∨ ((p3 ∨ True) → ((p1 ∨ p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754095460087025252472927501837 : (((False ∧ (((p5 ∧ False) ∨ p1) ∧ ((True ∨ ((((p1 → True) ∧ p5) ∨ ((False → p1) ∨ p5)) ∧ (p3 ∧ p4))) → ((p4 → p2) ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172135390270589779192811352139 : ((((p3 ∧ p3) ∨ ((p5 ∧ p2) → (p1 → (p1 ∧ p3)))) ∧ ((p5 ∧ p2) ∨ p1)) ∨ (p4 → (((p3 → p4) ∧ p3) ∨ ((p1 ∧ p1) ∨ p4)))) := by
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
theorem thm_5_vars_134040081887179573463647357692 : ((((((False → p3) ∧ ((True → p2) ∨ p1)) → ((p2 ∨ (p4 ∨ False)) ∨ (((True → p4) ∨ p1) ∨ p2))) ∨ False) ∨ p3) ∨ ((False ∧ p5) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807969042741936898670211221277 : (((p4 → ((p1 ∨ p1) → (((True ∧ (((((p2 → p5) → p2) ∨ False) → ((p5 ∨ p1) ∨ False)) ∨ p3)) ∨ (p2 ∨ False)) → (p5 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_405277392229600012526557566532 : (((((((False ∧ (p5 → ((p1 ∨ p1) ∨ True))) ∧ p4) ∨ (((p3 ∨ (False ∨ p4)) ∨ (False → (p3 → (p1 ∨ p1)))) ∨ False)) → False) → p4) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False ∧ (p5 → ((p1 ∨ p1) ∨ True))) ∧ p4) ∨ (((p3 ∨ (False ∨ p4)) ∨ (False → (p3 → (p1 ∨ p1)))) ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252481914289090723214984691279 : ((p5 → p1) ∨ ((p5 ∧ p2) ∨ (((((p2 ∨ ((p1 ∧ ((p5 ∨ p5) ∨ (False ∧ p2))) ∨ False)) ∨ p2) → p5) → False) → ((p1 ∧ True) ∨ True)))) := by
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
theorem thm_5_vars_118210482935848090823105514182 : ((p1 ∨ ((((p5 → (p2 ∧ (True ∨ (False ∧ (p5 → (((p5 → p1) ∧ p4) → p3)))))) → p3) → (p3 ∨ (p3 → p4))) ∧ p1)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153537270388918115635594524928 : ((True → ((p2 → (p5 ∨ ((True → p2) ∨ (p4 ∨ (p2 → (p1 ∧ True)))))) ∧ (False ∨ (True ∧ (p2 ∧ False))))) → (p5 ∧ ((False ∨ False) ∨ p5))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h10
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h11
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h14 =>
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178363413601548018209150097022 : (((p4 → ((p2 → ((p5 ∨ False) ∨ p3)) ∨ (p2 ∧ p4))) ∨ (p2 → p5)) ∨ ((((p4 → p5) ∧ (p2 ∨ p2)) ∨ p2) → ((p3 ∨ p3) ∨ p2))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164678439230613233286285747933 : (((((p2 ∧ (p3 ∧ (True ∨ (p4 ∨ True)))) ∨ (True → ((p1 ∨ p1) ∧ p4))) ∧ p1) ∨ p4) ∨ (True → ((p1 → (p5 ∨ (p2 ∨ p1))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663207425982840320553274690821 : (((((p5 → p4) ∧ (((p1 → (p4 ∨ (p4 → p1))) → (p3 ∧ p4)) → ((p4 ∧ p5) → (p3 ∧ ((p3 → False) → True))))) → (p1 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683840836042456972192384112832 : ((((((False ∧ p3) ∧ (((False ∧ p3) → False) → (False ∨ (p4 ∨ (p2 ∧ (False → p3)))))) ∨ p4) ∨ (p3 ∨ ((p5 ∨ p4) → (p1 ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228920446147699204422474921469 : ((p4 ∨ (p1 ∨ p1)) ∨ (p1 → ((((((((True ∨ False) → (p5 ∧ p1)) → p3) → p3) ∨ p2) → p1) → (p4 → p2)) → (p5 ∨ (p5 ∨ p1))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262329166677007476857859446776 : (True ∧ (((((False ∨ p3) ∨ p3) ∧ (False ∨ False)) ∧ (p1 → (((p4 ∧ p2) ∨ (((p5 ∧ p3) → (p4 ∨ p2)) ∨ (p1 ∧ p3))) ∧ p2))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210826646979732955212105821721 : (((p5 ∧ (True → True)) → True) ∧ (p4 ∨ (((p5 ∧ ((((p3 ∨ True) ∧ p4) ∨ p1) ∧ p1)) ∨ True) ∨ ((p4 ∨ p3) ∨ ((p4 ∧ p5) ∧ p5))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49516888895849534548094557629 : (((((True ∨ (p4 ∨ p1)) ∧ ((((p1 ∨ ((p1 ∧ p2) ∧ (p4 ∧ p5))) ∧ p1) ∨ p5) ∨ p3)) ∧ (p1 ∨ p1)) → ((p2 → p5) ∨ p1)) ∨ False) := by
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
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h12
          case inr h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h13
        case inr h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- Conjunctions on the left can always be decomposed.
          let h17 := h15.left
          let h18 := h15.right
          -- Conjunctions on the left can always be decomposed.
          let h19 := h16.left
          let h20 := h16.right
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h21 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h21
          case inr h22 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h22
      case inr h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h24
        case inr h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h25
    case inr h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h27
      case inr h28 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h28
  case inr h29 =>
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h31 =>
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h32 =>
          -- Conjunctions on the left can always be decomposed.
          let h33 := h32.left
          let h34 := h32.right
          -- Disjunctions on the left can always be decomposed.
          cases h33
          case inl h35 =>
            -- Disjunctions on the left can always be decomposed.
            cases h3
            case inl h36 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h36
            case inr h37 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h37
          case inr h38 =>
            -- Conjunctions on the left can always be decomposed.
            let h39 := h38.left
            let h40 := h38.right
            -- Conjunctions on the left can always be decomposed.
            let h41 := h39.left
            let h42 := h39.right
            -- Conjunctions on the left can always be decomposed.
            let h43 := h40.left
            let h44 := h40.right
            -- Disjunctions on the left can always be decomposed.
            cases h3
            case inl h45 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h45
            case inr h46 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h46
        case inr h47 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h48 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h48
          case inr h49 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h49
      case inr h50 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h51 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h51
        case inr h52 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h52
    case inr h53 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h54 =>
        -- Disjunctions on the left can always be decomposed.
        cases h54
        case inl h55 =>
          -- Conjunctions on the left can always be decomposed.
          let h56 := h55.left
          let h57 := h55.right
          -- Disjunctions on the left can always be decomposed.
          cases h56
          case inl h58 =>
            -- Disjunctions on the left can always be decomposed.
            cases h3
            case inl h59 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h59
            case inr h60 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h60
          case inr h61 =>
            -- Conjunctions on the left can always be decomposed.
            let h62 := h61.left
            let h63 := h61.right
            -- Conjunctions on the left can always be decomposed.
            let h64 := h62.left
            let h65 := h62.right
            -- Conjunctions on the left can always be decomposed.
            let h66 := h63.left
            let h67 := h63.right
            -- Disjunctions on the left can always be decomposed.
            cases h3
            case inl h68 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h68
            case inr h69 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h69
        case inr h70 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h71 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h71
          case inr h72 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h72
      case inr h73 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h74 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h74
        case inr h75 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h75



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753168818376071205445826199144 : (((False ∧ ((((p1 ∨ (p1 ∧ p2)) ∨ p4) ∧ ((True → ((p1 ∧ (((p4 ∧ p5) → p1) ∨ p5)) → p1)) → (p3 ∧ True))) ∧ (p4 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679925048159342478541567155077 : (((((((p3 ∧ p2) ∧ (True ∧ (p1 ∧ ((p5 ∨ ((p3 ∧ p1) → (True ∨ p3))) ∨ p4)))) → p3) → p4) → (((p2 ∨ False) ∨ p1) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165653019309369290573353626650 : ((((((p1 → True) → p2) → p1) → False) ∨ (p2 ∧ ((((p2 → p3) ∧ False) ∨ p1) ∨ p5))) ∨ (((True ∨ p3) ∨ p5) ∨ ((p4 → True) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152587077267842711681374868197 : (((True ∧ p5) ∧ ((p2 ∧ p4) → (p2 ∧ (p2 ∧ (((((p4 ∨ p5) → (p1 ∧ p4)) ∧ p5) → p4) ∨ False))))) → (p5 ∧ ((p3 → p2) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161040167829426658911139001976 : ((((p2 ∨ True) ∨ p5) → (((p3 ∧ p1) → ((p2 ∧ (False → p4)) ∧ (True ∧ (p4 → p1)))) ∧ False)) → ((False ∧ True) ∨ ((p5 ∧ p1) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∨ True) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245452838057796288402941920455 : ((p2 ∧ p4) ∨ (p1 → (((p4 → p3) ∨ (((((True ∧ (p5 ∨ False)) ∨ ((p2 → ((p3 → p4) ∧ False)) ∨ p4)) ∨ p1) ∧ True) ∨ p3)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113616439294827731155450978198 : (((p5 ∨ (True → ((((p1 → ((((p3 ∧ p2) ∧ p5) → p3) ∧ p2)) ∨ p5) ∨ ((p2 ∨ p1) ∧ True)) ∧ True))) ∨ (True ∨ False)) ∨ (p5 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655610925851707496871668431075 : (((((True ∨ ((((True ∧ (p1 → (False → p4))) ∧ ((p1 ∧ False) → (p3 ∨ (p1 → p1)))) ∨ p4) ∧ p4)) → (p4 ∧ False)) ∨ (p5 → p5)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336263216518979089480927745989 : (p1 → (((((False → p3) → ((p4 ∧ p2) ∧ (True → (p4 ∧ (False ∧ False))))) ∨ p4) ∨ (p5 ∨ (((True ∧ (p4 ∨ p3)) ∧ True) → p5))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314245347649967131592484921474 : (p3 ∨ ((((p1 → ((p4 ∨ p1) ∨ ((p4 ∧ p3) ∧ p2))) ∧ (((p5 ∨ False) → p2) ∧ p5)) ∧ (p1 ∧ (p2 ∨ p5))) ∨ (p4 → (True ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113572575549957509130583810994 : ((((p4 → True) → (p2 → (p4 → ((p2 → ((True ∧ p4) ∧ p4)) ∧ (p5 ∧ ((False ∧ p3) ∧ (p1 ∨ p5))))))) ∨ (False → True)) ∨ (False ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231504298463844536473097434631 : (((p3 → p5) ∨ p5) → ((((p3 ∧ (p5 ∨ (p1 ∨ p5))) → (p1 ∨ p4)) ∨ (p5 ∧ p3)) ∨ ((p3 → p1) ∨ (True → ((p2 ∨ True) → True))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676802602758452706013216798682 : ((((p2 ∨ ((((p2 → (p1 ∧ False)) ∧ (True ∧ ((p2 ∧ p2) ∧ ((p1 → p3) → p5)))) → False) ∧ False)) ∧ (((False → p2) ∧ True) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341737023176896183334302808742 : (p2 → (((p1 ∨ p1) ∨ (((p2 ∧ p1) → False) → (((False → (True ∨ (False → p1))) → (p1 ∨ p5)) ∨ (p3 → (p5 ∨ p5))))) ∨ (p2 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688972546271451274134975842722 : ((((((((p3 ∨ p1) ∨ p1) ∨ ((((p3 → p2) → p5) ∧ True) ∧ True)) ∧ p4) ∨ True) ∨ (False → (p2 → (((False ∨ p2) ∨ p5) → p5)))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_118507614625868339300442491486 : ((p3 ∨ ((p3 → (((p4 → True) ∧ True) ∧ False)) ∨ ((p5 ∧ p4) ∨ ((((p2 ∨ (True ∨ p2)) ∧ True) ∨ (False ∧ True)) ∨ p2)))) ∨ (p5 ∧ False)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39683726146827751354890684293 : (((p4 ∨ ((True → (((False ∧ (p3 ∨ p2)) ∨ True) → ((False ∧ True) ∧ (p4 ∨ (True → p2))))) ∧ (p5 → (p1 → (p3 ∧ p2))))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740137752856629368359701682743 : ((((False ∨ p3) ∨ ((p5 ∧ (p3 ∧ p3)) → (p4 ∨ ((p1 ∧ (p2 ∨ p1)) ∧ ((p4 ∧ ((p2 → p1) ∨ (False ∨ (p4 → p5)))) ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323583793199025083052651870847 : (p5 ∨ ((p2 ∧ ((p1 → True) ∨ (False → (False ∧ ((True ∨ (p2 ∨ (p1 ∧ ((p2 ∧ p3) → (p4 ∨ p5))))) ∨ p2))))) → ((p2 → False) → p5))) := by
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
  cases h4
  case inl h5 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229439512804491080349968830744 : ((p1 → (p2 → p4)) ∨ (((((p4 → p4) ∨ ((p4 → (((((p5 → True) ∨ True) ∧ p4) ∧ p3) ∧ (p5 → p2))) ∨ p1)) → p3) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135123338678985617544152688380 : (((True ∧ (((((p3 ∧ p3) ∧ (False → p5)) ∨ p1) ∨ ((p3 → (p5 ∨ (p1 ∨ p4))) → p4)) → p4)) ∨ (False → False)) ∨ ((True ∧ p1) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51654763270287793983295969754 : (((((((p2 ∨ (((p4 ∨ (p4 ∧ p1)) ∨ p1) ∧ p2)) ∨ p3) ∨ p5) ∨ p4) → p4) ∧ ((p2 → (p1 ∨ ((False ∨ p1) → p2))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44119997823927907962865499918 : (((((((p4 → True) ∨ (p3 ∨ p4)) → (p1 ∧ (p2 ∧ True))) → ((p1 → (p1 → p4)) ∨ (False ∧ p1))) ∨ ((p3 → p4) ∨ True)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190758059101426484482540926109 : (((p2 → (((p4 ∨ p4) ∧ p2) ∨ p1)) ∧ (False ∧ p2)) ∨ (True → ((False → False) ∧ (((((p5 → p4) → p3) ∨ p1) ∨ p4) → (False → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



