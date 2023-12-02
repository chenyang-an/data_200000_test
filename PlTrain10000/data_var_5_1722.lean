variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732946547621581662763891877660 : ((((p2 ∧ p2) ∧ (p1 → (((p4 → p3) ∨ (True ∨ (p5 ∧ p3))) → (((p1 ∧ ((p5 → (p5 → True)) → p3)) → p2) ∧ (True → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64681553909585482250687589752 : ((p1 ∨ (p4 ∨ (((False → (((p5 ∧ p5) ∨ (p3 ∨ ((p3 ∧ p5) → (((True ∨ p1) → p3) ∧ p1)))) ∨ (p1 ∨ p4))) ∧ p2) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52060220632911220502056183738 : (((p5 → ((((p5 → (p2 → p2)) ∨ p2) ∧ (False ∨ p3)) ∧ ((p4 ∧ False) ∧ p5))) ∨ (False ∨ (p1 ∨ (True ∧ ((p1 ∨ p5) → True))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136490449409323176965477516466 : ((((p1 ∧ p1) → False) ∧ ((p4 ∧ (p4 ∨ p4)) → ((((p3 ∨ (False → (True ∨ p5))) ∧ p1) → p2) ∧ (p2 → p2)))) ∨ (p4 ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353533573245480777027790658297 : (p4 → (p3 ∨ ((((((p2 → p4) ∧ False) ∧ (p2 ∧ p3)) ∧ ((p4 ∧ p3) ∧ p4)) ∨ ((p3 → p2) ∨ (p1 → (True ∧ (False → p1))))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41621412430002622655267792047 : (((((p4 ∧ ((p4 ∧ p2) → (False ∧ p1))) ∨ False) → ((p3 → False) ∨ ((((True ∨ False) → (p5 → (p3 ∨ False))) → p1) ∨ p4))) ∨ p3) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54660617682454474744014351304 : ((((p1 ∧ ((p1 ∧ (False → p2)) ∧ p1)) ∨ True) → ((((((((p5 ∨ p4) ∧ p5) ∨ p2) ∧ p5) → p3) ∨ False) → (True ∧ False)) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160019809719419825495830431206 : ((((False ∨ (p3 → p4)) ∨ (p4 → (((((False → p5) ∧ (p1 → p5)) ∧ p2) → p5) ∨ False))) → True) → (p4 ∨ ((True ∨ (p1 ∧ True)) ∨ p4))) := by
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
theorem thm_5_vars_797321459180615813337559562505 : (((p1 → (((p3 ∧ ((p4 → (p5 ∧ (p3 ∨ (True ∨ ((p1 → (p1 ∧ p5)) → (True ∧ p2)))))) ∨ p2)) → ((p2 ∧ p5) ∨ p3)) ∨ p4)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114163015926707164858215486551 : (((((p2 ∧ ((p3 ∧ p1) ∨ (True ∧ True))) ∨ ((p3 ∨ (False ∨ True)) ∨ ((p1 → p5) ∧ p1))) → p1) → ((p4 → p5) → p1)) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114714923217599245677473733895 : ((((p5 ∧ (((True ∨ (((p2 ∨ True) ∨ p2) → (False ∧ p5))) ∧ p1) ∧ p1)) → True) → ((p3 ∨ (p3 → True)) → (p3 ∧ p2))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137363227150526294213020399045 : ((p3 ∧ ((p3 ∨ ((((True ∨ (p3 ∨ p4)) → False) → (False → (((p5 ∧ p3) ∧ p1) ∧ (p3 ∨ p4)))) ∧ p3)) → p4)) ∨ ((p4 ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748394447261532143798756001615 : ((((p2 → p3) → (((p5 → False) ∨ (((((p5 ∨ p3) → ((p3 ∧ p5) ∧ p3)) ∨ p5) → (p5 → p2)) → False)) → (p3 ∧ (p1 → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137632847742598875071447335615 : ((False ∨ ((((((((p1 ∧ p2) → p5) → p5) ∧ p2) ∧ p5) ∧ (p1 ∧ p2)) ∨ (p2 → (p1 → p2))) → (p5 ∨ p1))) ∨ (p5 → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204155659307978655989971384440 : (((((p1 ∨ p1) ∨ False) ∨ p3) ∧ p4) ∨ (False → (False ∨ ((p3 → True) ∧ ((p4 → (((False → p5) → p4) ∧ (False ∨ (True ∨ p3)))) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305526800677390184897617299255 : (p1 ∨ ((((p4 ∨ (p5 ∨ (p3 → ((False → p3) ∧ p4)))) ∨ True) ∨ (p2 → p3)) → (((p2 ∧ p3) ∨ p1) ∨ (p1 → (p5 → (True ∧ p1)))))) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h5
        -- Implications on the right can always be decomposed.
        intro h6
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h9
          -- Implications on the right can always be decomposed.
          intro h10
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- Implications on the right can always be decomposed.
          intro h13
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h12
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Implications on the right can always be decomposed.
      intro h16
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- Implications on the right can always be decomposed.
    intro h19
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171688727231984538991347735252 : (((p5 ∨ (((((False ∧ p1) ∧ p3) → (True → (True ∧ p4))) → p3) ∨ True)) ∨ p4) ∨ ((((p4 → ((p4 ∨ p4) ∧ False)) ∨ True) → p5) → p1)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689100685475359661858133932789 : (((((p4 ∨ ((True ∧ (p4 → ((p1 → p4) → p2))) ∧ (p4 ∧ (p4 ∧ p3)))) ∨ p2) ∨ (p2 → ((p4 ∧ (p3 ∨ False)) ∧ (p4 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327056929038571100738416350995 : (True → (((False ∨ ((False ∨ (True ∧ False)) ∨ p1)) ∨ (((((((p3 ∧ (p5 ∨ p4)) → p3) → (p3 → p3)) ∨ False) ∧ p2) ∨ p4) ∨ True)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137645416317770623572644550358 : ((False ∨ (((p2 ∨ ((p4 → True) ∧ p2)) ∧ False) ∨ (p1 → ((p1 → p4) ∨ (p4 ∨ ((p2 → (p1 ∧ False)) ∨ p1)))))) ∨ (p4 ∨ (p4 → p1))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651585473440512678395955336255 : (((((p5 ∨ p5) ∧ (p2 ∧ ((((p5 ∨ p4) ∧ ((False → p4) → p2)) ∧ p1) ∨ (((True ∧ p2) ∨ (p3 → p3)) ∨ p2)))) ∧ (True ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41654613725810041676874854329 : (((((p2 ∧ p2) → ((p3 ∨ p5) ∨ p2)) ∧ (((((p5 ∨ True) ∧ p2) → False) ∨ False) → (((p1 → p5) ∧ p5) → (p5 ∧ False)))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785378681249180849736277960196 : (((p4 ∨ (((p1 ∧ ((p2 ∧ ((True ∨ (((p3 → (p3 ∧ True)) ∨ p3) ∨ p3)) ∧ (p3 ∧ (p5 → p3)))) ∨ (False ∨ p1))) → p4) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_779574346375376319406736933829 : (((p2 ∨ ((p4 ∧ ((False ∧ (p1 ∨ (p3 ∧ ((True ∨ (p1 → (p2 ∨ p5))) ∧ (((p1 ∨ p3) ∨ True) → p3))))) ∧ (False ∧ p4))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56852649618740688074830447994 : (((True ∧ (p3 → p2)) ∧ (((p5 ∧ (p2 → p5)) ∨ (False → (True ∨ (p2 → (p1 ∨ ((True ∧ False) ∨ (p1 ∨ p1))))))) ∧ (p2 → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67755131459500096802035102419 : ((p2 → (((((((((p4 ∨ False) ∧ p5) → p4) ∧ (p3 → p2)) → (p4 ∧ p3)) → p3) → (p3 → (p3 → (p3 ∨ False)))) → p3) ∨ p2)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168864214736202649124821838140 : ((p4 ∨ ((p5 → (((p2 ∨ (p5 ∨ p4)) ∨ (((p3 ∧ True) ∧ False) ∨ p2)) ∨ False)) ∨ False)) → (p4 → (((p4 ∧ p1) → (False ∧ True)) ∨ p4))) := by
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
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175256041360745921884355500481 : ((p2 ∨ ((((p3 → p2) ∧ (False ∨ ((True → p4) → p5))) → True) ∧ (p4 ∧ p2))) → (p5 ∨ (p4 ∨ (True ∨ ((p1 → (p1 ∨ False)) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747402460697767077943549342232 : ((((True → True) → ((((p5 ∧ ((((True ∨ p3) → (False → (p1 → p4))) ∨ p2) ∧ ((p4 ∧ p3) → (True ∨ p5)))) → p1) ∨ p1) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160378970016173546872624073968 : ((((p2 → False) ∧ ((p5 ∧ p5) → ((p3 ∧ (False ∧ p3)) → (False → True)))) ∧ (p2 ∧ (p5 → True))) → (((p3 → True) ∧ (p3 ∨ p5)) ∨ p3)) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59594196219708047677075553517 : (((p4 → p2) ∨ ((((p5 ∧ ((((False → p4) → p4) ∨ p4) ∨ p3)) ∨ p1) ∨ True) ∨ ((p5 → (False → (p4 ∧ p2))) ∨ (p2 → p1)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301558235645570056163232139785 : (False ∨ ((p4 ∧ (False ∧ True)) ∨ (((p1 ∧ p5) ∨ (p2 ∧ p4)) ∨ (((p4 ∨ ((((p1 ∨ p5) → p1) → (p5 ∧ p3)) → p2)) ∧ p3) ∨ True)))) := by
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
theorem thm_5_vars_185249594123455954935154168038 : ((p1 ∧ ((((p2 ∧ (p1 → p1)) ∨ (p4 ∨ False)) → p1) ∨ p3)) ∨ (False ∨ (((p2 ∧ p3) → (((True ∨ False) ∧ p1) ∧ p1)) → (p2 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767273178573240862652445118642 : (((p5 ∧ (((((p3 → (True ∨ p5)) ∨ ((p3 → p5) ∨ True)) ∧ ((p3 ∧ (p2 ∧ (p3 → (p1 ∨ p3)))) → p2)) → (p4 ∨ p5)) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617946930149343574249418819920 : (((((p5 ∨ ((False ∧ p1) → (p2 ∧ True))) → (False ∧ ((((True → (p2 → p5)) ∧ (p5 → p4)) ∧ ((True ∧ p3) ∧ p1)) → p5))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227442081820709693662114142850 : (((p5 → p4) → p2) ∨ ((p1 ∧ (p3 ∨ (p5 → False))) ∨ ((p5 ∧ (False ∧ (True ∧ ((((p1 ∨ p5) ∨ False) → (p1 ∧ p3)) → p1)))) → p5))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319680019173838140412917539504 : (p4 ∨ (((p3 → p3) → ((True ∧ (p2 → p3)) ∧ p4)) → (p5 → ((False ∨ ((True ∧ ((True → ((True ∧ p3) → p1)) ∧ p1)) ∧ p1)) ∨ True)))) := by
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
theorem thm_5_vars_330898554013071676592266107247 : (True → (p4 → ((((p5 → ((p1 ∧ p5) → (True ∧ p5))) → ((p4 ∧ p2) ∧ False)) ∨ (p4 ∧ (((p1 ∧ (p2 ∧ p4)) ∨ True) ∨ p4))) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134042703762047792821427640189 : ((((((p4 → p4) ∧ p4) ∨ (p1 ∨ (p2 ∨ ((False ∨ (False ∨ ((p4 ∨ True) → (p3 ∨ p1)))) ∧ p4)))) ∨ p1) ∨ True) ∨ (p2 ∧ (p2 → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318477282434909771390028901887 : (p4 ∨ (((((p5 ∧ ((False ∨ p4) ∨ ((p2 ∧ (p3 ∧ p1)) → p3))) → False) ∧ p1) → (p5 → (True ∧ ((p5 → p5) → p3)))) ∧ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p5 ∧ ((False ∨ p4) ∨ ((p2 ∧ (p3 ∧ p1)) → p3))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h12 := h4 h6
  -- False on the left can always be used.
  apply False.elim h12
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232175325556609633456651952071 : (((False → True) → False) → (p5 ∧ (p2 ∧ (p1 ∨ ((p3 ∨ ((((p5 → p3) → ((p4 ∨ p1) ∨ p5)) ∨ p5) ∨ (True ∨ (p2 ∧ False)))) ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (False → True) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (False → True) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h8
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2491616900790614950583085349 : ((((p4 ∧ p1) → (p1 → p2)) → (p4 ∧ (p4 → p3))) → (p1 → (((((p4 ∨ p1) ∨ (p5 ∧ True)) → (True ∧ p5)) ∨ p1) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307455264457910074221317195459 : (p1 ∨ (p5 ∨ ((True → (p4 ∨ True)) → (p4 → (((p3 → False) ∨ ((p1 ∨ (p5 ∨ (False → ((p4 ∨ True) → True)))) → (True ∨ False))) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247380952647134431702193043853 : ((False ∨ p1) ∨ ((p2 ∨ p5) ∨ ((((((p5 → False) → (((p4 ∧ False) → p3) → True)) → (p5 → p5)) ∧ p3) → p2) ∨ ((False → p2) ∨ p5)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172969711940610077429461729946 : ((p4 ∧ (((p2 ∨ p4) ∧ (True ∨ p2)) ∧ (p2 → (((p5 ∨ p5) → p3) → p4)))) ∨ (p1 ∨ ((p5 ∨ (((False ∨ p2) → p4) ∧ True)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173054070447328167859231557054 : ((False ∨ (((p3 → p3) ∧ ((p4 ∧ (p5 ∧ (p1 → p4))) ∨ p4)) ∧ (p1 → True))) ∨ (True ∨ ((((p2 ∧ (p3 ∨ False)) ∧ p1) ∨ False) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51869475381347834871522453296 : ((((((True → False) ∧ p2) ∧ (((((p4 → p1) → False) → p2) → p2) → p4)) ∨ False) ∨ (p2 ∨ (p2 ∨ ((p1 → True) ∨ (p3 ∧ False))))) ∨ p4) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112560591329826840844121328018 : ((((False ∧ (False ∨ (False ∧ (((p4 → p4) ∧ ((True ∨ (False ∧ True)) → (((p1 → p2) ∧ p5) → p4))) ∨ True)))) → False) → p4) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722979817976273442285609234529 : (((((True ∨ p3) ∨ False) ∧ (p2 → ((p2 → (p1 → (p1 ∧ p1))) → (p5 ∧ (p5 ∨ (((p5 ∧ ((p1 → p2) ∨ p2)) ∨ False) ∨ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114009538127696670990067201600 : (((((True → True) → (((((p4 ∨ p2) ∧ p3) ∨ (p2 ∨ (True → (p1 ∨ True)))) → True) → p1)) ∧ p3) ∨ (p4 → (p1 → True))) ∨ (p4 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312447634018140149193480686548 : (p2 ∨ (p4 → (True ∧ ((((False ∧ (p5 → (((p4 ∧ p4) ∧ p5) → ((p1 ∨ (p1 ∨ p1)) ∧ p1)))) ∧ (p3 ∧ (False ∨ p3))) ∨ True) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174953336636510334786540551098 : ((True ∧ (((True → (True ∨ ((True ∧ (p4 ∧ (p5 ∨ True))) → p5))) ∨ True) → p5)) → ((p3 ∨ (p5 ∨ (((p4 ∨ p2) ∧ p4) ∨ p2))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((True → (True ∨ ((True ∧ (p4 ∧ (p5 ∨ True))) → p5))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44420739801500728413680730150 : ((((p1 → ((p2 → (((((True ∧ p4) ∨ p5) → p2) ∧ True) → True)) ∧ True)) → (((p2 ∨ ((p4 ∧ p3) → p1)) ∨ p5) ∧ p2)) → p2) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → ((p2 → (((((True ∧ p4) ∨ p5) → p2) ∧ True) → True)) ∧ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791945676829373444525584116491 : (((True → ((p1 ∧ (((p1 ∨ ((True ∧ p3) ∨ p3)) → p5) ∧ ((p2 ∧ False) ∨ ((p2 ∧ p1) ∨ (True ∧ (p3 ∨ p5)))))) ∨ (p2 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3143874067528449511394501286 : ((False → p4) ∧ ((p2 ∨ (False ∧ p4)) ∨ ((((p3 → (p1 → (((p2 ∨ p1) ∨ True) ∧ ((p1 → p5) ∨ False)))) ∨ p1) ∧ p3) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219437141782920861706634992287 : ((p4 ∨ ((p4 → p2) ∨ True)) → (p5 ∨ (p4 ∨ (True ∨ (p4 ∧ ((True → p2) → (p2 ∧ ((False ∧ (((p4 ∨ p3) ∨ True) → p4)) ∨ p1)))))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807345181047427240984137960504 : (((p4 → ((p2 ∧ ((((p4 ∧ False) → p2) ∧ (p2 → p2)) ∧ (p1 ∨ p4))) → (((p3 → (p2 → True)) ∨ ((True → False) ∨ p3)) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358353223942143494067180246440 : (p5 → (True → ((((False ∨ p4) → ((((p5 ∧ p2) ∧ p4) ∧ (True ∧ (p2 → ((True → p4) ∧ False)))) ∧ p4)) → False) ∨ ((True ∨ True) → True)))) := by
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
theorem thm_5_vars_139816720810402117953751931476 : (((True → ((p4 ∧ (((p4 ∨ ((p3 ∨ ((p3 ∧ p3) ∧ p2)) ∧ True)) ∧ True) ∨ (p3 ∧ p4))) ∨ (p4 ∨ True))) → p3) → (p3 ∧ (p1 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → ((p4 ∧ (((p4 ∨ ((p3 ∨ ((p3 ∧ p3) ∧ p2)) ∧ True)) ∧ True) ∨ (p3 ∧ p4))) ∨ (p4 ∨ True))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253965564632486097878665341725 : ((p1 ∧ p5) → (((p3 ∨ ((((p5 ∧ (p3 ∧ p2)) → p2) ∧ p2) ∨ ((p3 ∧ (p2 ∨ p5)) → ((False ∨ p3) → (True ∧ False))))) ∨ p3) ∨ p1)) := by
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
theorem thm_5_vars_615023396513515939796866489393 : ((((((p3 ∧ p2) → (p1 ∨ (p2 ∨ ((p4 → p3) ∧ (True → (p4 ∨ (False → (p3 ∧ False)))))))) → ((p5 ∨ (p4 ∨ p5)) ∧ p3)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60108680569555273147778886359 : (((p3 ∨ p2) → (p3 → ((((p2 → p1) → False) ∧ p3) ∨ ((p1 → (p3 ∨ (((p3 → p1) → (p5 → (p3 → False))) → p4))) ∨ True)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702874563327237503092311497398 : (((((((False ∧ p4) → p3) ∨ True) → (p3 ∧ (p3 ∧ p5))) ∨ (True ∧ (p3 → ((p3 ∨ (p2 ∧ ((p5 ∧ (p3 ∨ p1)) ∨ p3))) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234311412161510746505161961606 : ((p1 → (p1 ∧ True)) → (p1 → ((p1 → (p4 ∨ (False ∧ (p3 ∧ p3)))) ∨ (p5 → (((p4 → (p4 ∧ ((p4 ∨ p1) ∧ p5))) ∧ p1) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136718322012578618457179837978 : (((p3 ∧ p4) ∧ (((True ∨ p5) → p4) ∨ ((True ∨ (p1 ∨ (p3 ∨ False))) → (p5 ∧ (((p5 ∨ p4) ∨ p2) ∧ p5))))) ∨ (p5 ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50185832595934348777833386290 : ((((((p1 → (True → p5)) ∧ False) ∨ ((p3 → (p2 ∨ p2)) ∧ ((p3 → p5) ∧ (True ∧ p4)))) ∧ p1) ∨ ((p5 ∨ p4) ∨ (p4 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50652518075567860152073719103 : ((((((p1 ∨ (True → False)) → p4) ∨ (p3 ∨ (p2 ∨ True))) → ((p4 ∧ (p1 → (p3 → p1))) ∧ False)) → ((False ∨ (p1 ∨ True)) ∧ False)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ (True → False)) → p4) ∨ (p3 ∨ (p2 ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
theorem thm_5_vars_586630047217891998549124466920 : ((((((p2 ∧ True) → ((p4 → (p5 ∨ (((p4 ∧ (p1 → False)) ∨ (((p1 ∨ True) → p5) ∨ (p2 ∧ p5))) ∨ p2))) ∧ p4)) ∧ p3) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337366920114835951789352373068 : (p1 → (((((False ∨ (p2 ∨ (False → False))) → ((p2 → p3) → p3)) → True) → ((True → ((p4 → p5) ∧ False)) → p3)) ∨ (p2 → (p3 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806968822407903526944792024225 : (((p4 → (((((p1 ∨ p2) → ((((p4 ∨ (p3 ∨ p3)) → (p3 ∧ p5)) ∨ (False ∧ p5)) ∨ p2)) ∧ p4) ∨ p5) ∨ ((p5 ∨ True) ∨ p3))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336954047982132586868179956711 : (p1 → ((((p4 ∧ p2) → ((p3 ∨ ((p4 ∧ p3) ∧ (p1 → p3))) ∨ ((((False ∧ p1) → p4) → p3) ∧ p2))) ∨ (p5 → True)) ∧ (p1 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653693373090325324815554210764 : (((((((p5 → (p4 → (p4 → True))) → ((p4 ∨ p1) → (p1 → (p1 ∨ ((p3 → (p5 → False)) ∨ p4))))) → False) ∧ p1) ∨ (p2 → True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_266256870247999045398227460495 : (True ∧ (p5 → ((((True ∨ (p4 → (True ∧ (p1 → p1)))) ∧ False) ∨ ((True → (p5 ∧ p2)) → ((p2 ∧ p2) ∧ p4))) ∨ ((False ∧ p3) ∨ p5)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46860466146833996505465339681 : ((((p4 ∧ (((((p2 ∨ p3) ∧ (True ∧ (True ∧ p1))) ∧ p1) ∧ (p4 → (p3 ∧ ((p4 ∨ p2) ∨ p3)))) ∨ False)) ∧ p3) ∨ (False ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762163529420447672363308229480 : (((p3 ∧ (((p2 → ((p5 → (False ∧ ((p2 ∧ (p4 ∨ (p4 ∨ True))) ∨ False))) ∨ p5)) ∨ (p1 ∨ (p1 ∧ (p2 ∧ True)))) ∨ (p5 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729906354255770847593526146996 : (((((p2 ∧ p5) → p3) → (p2 ∧ (p5 ∨ (p1 → (((p4 → (((True → False) ∨ p5) ∨ p4)) ∧ p3) → ((p1 ∨ (True ∧ p2)) ∨ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196921519515756753409544879753 : (((((p3 ∧ p1) ∨ (False ∧ p3)) ∧ p1) ∨ p5) ∨ ((((p2 ∨ p2) ∨ True) → p3) ∨ (((p1 ∧ p2) → (False ∧ p5)) ∨ (p3 ∨ (True ∨ p5))))) := by
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
theorem thm_5_vars_47063284764908269549907319568 : ((((((p2 ∧ p1) ∧ ((p4 ∨ False) ∧ (p1 ∨ (p2 ∨ False)))) ∨ (p4 ∧ (True → ((p4 → True) ∨ p3)))) ∨ (False → p2)) ∨ (p2 → p4)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_469289868748160047600996348771 : (((((False → (p3 → p4)) → (p2 → (p5 → (((p2 ∨ p5) → False) ∧ p3)))) → ((p3 → (True ∧ p3)) ∧ ((True → p4) ∨ (p1 ∨ True)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135425867966505876011538257027 : (((p5 ∧ ((p3 ∨ True) → (((p2 → (False ∨ p4)) ∨ p4) → ((p3 ∨ (p3 ∧ False)) ∨ True)))) ∨ ((p2 → False) → False)) ∨ ((p1 ∨ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51939546936257881466668266915 : (((((True → p3) → ((p2 ∧ (p1 → p1)) → p1)) ∨ ((p4 ∨ True) ∨ (p2 → p3))) ∨ ((p4 ∧ p2) ∨ (p5 → (True → (True ∧ p2))))) ∨ p1) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254585477376212025035670744636 : ((p3 ∧ p1) → (((((p3 → (p3 ∧ p1)) ∨ (p2 → p1)) ∧ (p2 → p5)) → ((((p1 ∧ True) ∧ p3) ∨ p4) → (p3 ∧ p4))) ∨ (p3 ∨ p2))) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127926668130483058645758287678 : ((False → ((p4 → p2) → (p4 ∨ ((((p4 ∨ (p5 ∨ p4)) → (((p2 ∧ (p2 ∧ p4)) ∧ p1) ∨ False)) ∨ (p5 ∨ p4)) → p3)))) → (p3 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229727719633477629476209935848 : ((p4 → (p4 ∧ p5)) ∨ (p4 ∨ (((p2 ∨ ((False ∨ p2) → ((p1 → ((True ∨ False) → p2)) ∧ (p5 ∧ False)))) ∧ (p2 ∨ (p1 ∨ p3))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232375622723889388643485313945 : (((p5 → True) → p5) → (((False ∨ (p3 → False)) → (((((p3 ∨ p1) → p2) → True) → p4) ∨ (p5 → ((p1 ∧ (False ∧ False)) ∨ p1)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586433811080038758761701105161 : (((((((True ∧ True) ∧ p4) ∧ ((((p5 ∨ ((False ∨ p3) ∧ p4)) ∧ (p1 → (((p2 ∨ False) → p3) → p2))) ∨ p3) ∧ False)) ∧ p5) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64088272173022883076145000614 : ((False ∨ (((p1 ∨ ((((p2 ∨ p1) → (False → p3)) → p4) ∨ True)) → p2) ∨ (p2 ∨ (((False ∧ ((False → p2) → False)) → False) ∨ p5)))) ∨ p5) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179697459487450562730037363541 : (((((p3 ∨ ((p5 → ((p1 ∨ p2) ∧ p5)) ∨ p3)) ∨ False) ∨ p1) ∧ True) → (False ∨ (p3 ∨ (((p3 ∧ False) ∧ (p4 ∨ (p5 ∨ p2))) → p2)))) := by
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
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h9
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Conjunctions on the left can always be decomposed.
          let h12 := h10.left
          let h13 := h10.right
          -- False on the left can always be used.
          apply False.elim h13
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h14
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h17
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h18.left
    let h21 := h18.right
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_465204072519183100514166897547 : ((((p1 ∨ ((p4 ∨ ((p1 → p1) → False)) ∨ ((p2 ∨ p1) ∨ ((p5 ∧ p5) → True)))) → (p4 ∨ ((False → ((p1 ∧ p1) ∧ True)) ∨ p1))) ∧ True) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h6 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h7 : (p1 → p1) := by
          -- Implications on the right can always be decomposed.
          intro h8
          -- One of the premise coincides with the conclusion.
          exact h8
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h9 := h6 h7
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h13
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- False on the left can always be used.
          apply False.elim h13
          -- False on the left can always be used.
          apply False.elim h13
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h16
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h16
        -- False on the left can always be used.
        apply False.elim h16
        -- True on the right can always be proven directly.
        apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49171103505159996780853279571 : (((((p1 ∨ False) ∨ ((p2 → False) ∨ p1)) → (((p4 ∧ (False ∧ p5)) ∨ True) ∨ (p4 ∧ ((p5 → p5) → p2)))) ∨ (p5 → (True ∨ p4))) ∨ p3) := by
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
theorem thm_5_vars_131272745403984941534958330860 : ((((p1 ∨ (p3 ∨ p2)) ∨ (p5 → p2)) ∨ (((((p3 → p4) → (p4 → p5)) ∧ p2) ∧ (p2 ∧ (p4 ∧ p5))) → p2)) ∧ ((p2 ∨ True) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214570085372859213696550081839 : (((p2 ∨ p1) ∧ (p4 ∧ p1)) ∨ (((p4 ∨ ((((p3 ∨ ((p1 → p5) ∧ p3)) ∨ p5) ∧ (p5 ∨ False)) → p1)) → (p2 ∧ True)) → (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196926903789387362776119598431 : ((((p1 ∧ (p4 ∨ (p4 ∧ False))) ∧ False) ∨ False) ∨ ((((True → (True → (p5 → False))) ∨ (((p1 ∧ p3) ∧ p5) → True)) ∧ True) ∨ (True ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1813334371600579782002518244 : ((p1 ∨ ((p4 → p2) → ((p5 ∨ True) → (True ∧ ((False → p4) → ((True → (False ∧ p3)) → (False ∨ p5))))))) ∨ ((p5 → p2) → p4)) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720097180544002915860631184004 : ((((((p1 → p4) → p3) ∧ p2) → ((p2 ∧ ((p1 → True) ∨ (((False → ((p1 → p3) ∧ p2)) ∨ p4) → p1))) → (True → (True ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315010757348983727167103826019 : (p3 ∨ (((((p3 ∧ (p2 → True)) ∨ p4) ∨ p5) → p2) ∨ ((True ∧ (((p4 ∧ (True ∧ ((True → p2) ∨ p1))) ∨ p2) ∨ (False ∧ p4))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329581256597599511435897765518 : (True → ((p5 ∨ p1) ∨ (p3 ∨ (p3 → (((True ∨ ((p1 ∨ (False ∧ ((False ∨ False) ∧ (True ∧ p4)))) ∨ False)) ∧ False) ∨ (p5 ∨ (False → p5))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152082245590042005347643321194 : (((((((True → p2) ∧ p1) → False) → (p1 ∧ True)) ∨ True) → (p2 → ((p4 → (p3 ∧ p3)) ∨ (True ∧ True)))) → (p2 ∨ (p5 ∨ (False → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_957671375557124752261030657371 : ((((p2 ∨ (True ∨ True)) → ((((False ∨ True) ∧ (p4 ∨ ((((((p2 ∧ False) ∧ p1) ∨ p4) ∧ p5) → p5) ∧ p3))) ∧ False) ∧ (False ∨ p5))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ (True ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157982986910614459367276320461 : ((((((p1 → p3) ∨ p2) ∧ (p3 ∧ p4)) ∨ True) → (((p5 ∨ p4) ∨ False) ∧ (p1 ∨ (False → p5)))) ∨ ((p5 → p4) → (p3 ∨ (True → True)))) := by
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



