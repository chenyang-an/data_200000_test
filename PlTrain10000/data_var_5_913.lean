variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245571933031910893425823619590 : ((p3 ∧ True) ∨ (p5 ∨ ((((p4 ∨ ((((p3 ∧ p3) ∨ p1) ∨ p3) ∧ True)) ∨ ((p2 ∨ (p3 ∧ p5)) → (p2 ∨ p5))) ∧ (p1 → p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312442129411024571826742412027 : (p2 ∨ (p4 → (((p5 ∧ p1) ∨ p4) → (((p5 ∧ (((p5 ∧ (p4 ∧ p2)) ∧ (False ∨ p2)) → p1)) → ((p3 → p4) → (p2 ∧ False))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_342832443916365288208703981479 : (p2 → ((p2 ∧ ((False → p3) ∧ (p4 ∨ True))) ∧ ((p3 ∨ (p3 → (p1 ∨ ((p1 → False) ∨ (p2 → p5))))) ∨ (True ∨ ((p5 ∨ p3) ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315495305430677558032803989920 : (p3 ∨ ((p5 ∧ (p3 ∧ True)) → ((True ∨ p4) ∧ (((p4 → (p1 → p4)) ∨ (True ∨ ((p1 ∧ p5) ∨ p3))) → (p1 → ((p4 ∨ p5) ∧ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h1.left
      let h16 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- Conjunctions on the left can always be decomposed.
        let h23 := h1.left
        let h24 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h23
      case inr h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h1.left
        let h29 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h28
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h32 =>
    -- Conjunctions on the left can always be decomposed.
    let h33 := h1.left
    let h34 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h35 := h34.left
    let h36 := h34.right
    -- One of the premise coincides with the conclusion.
    exact h33
  case inr h37 =>
    -- Disjunctions on the left can always be decomposed.
    cases h37
    case inl h38 =>
      -- Conjunctions on the left can always be decomposed.
      let h39 := h1.left
      let h40 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h41 := h40.left
      let h42 := h40.right
      -- One of the premise coincides with the conclusion.
      exact h39
    case inr h43 =>
      -- Disjunctions on the left can always be decomposed.
      cases h43
      case inl h44 =>
        -- Conjunctions on the left can always be decomposed.
        let h45 := h44.left
        let h46 := h44.right
        -- Conjunctions on the left can always be decomposed.
        let h47 := h1.left
        let h48 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h49 := h48.left
        let h50 := h48.right
        -- One of the premise coincides with the conclusion.
        exact h47
      case inr h51 =>
        -- Conjunctions on the left can always be decomposed.
        let h52 := h1.left
        let h53 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h54 := h53.left
        let h55 := h53.right
        -- One of the premise coincides with the conclusion.
        exact h52



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209176427689868838305842190938 : ((p4 ∨ (((p5 → True) ∧ False) ∧ p4)) → (((((p4 ∧ p4) ∧ ((p2 ∨ ((p2 ∨ p3) ∧ p5)) ∨ p5)) ∧ ((p4 ∧ p5) → False)) ∨ p2) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612982598372252315973348541595 : (((((((((((True ∨ ((((True → True) → False) → p1) → p4)) ∨ p4) → p1) → (True → p4)) → p1) ∧ p2) ∧ p1) → (p4 ∨ p2)) ∨ p5) ∨ False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115471634873277779284984080388 : (((p3 ∨ ((p3 ∧ ((p5 → p2) → p5)) ∧ p5)) ∨ ((p1 ∧ ((False → (True ∨ p5)) ∨ p1)) ∧ ((p4 ∧ p2) ∨ (False ∨ p1)))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621287265733851509965053564641 : ((((True ∧ ((((((p1 → False) ∧ p4) ∨ p1) ∨ ((p2 ∨ p3) ∧ True)) ∧ p1) ∧ (p1 → (((p4 ∧ True) ∧ (p1 ∨ False)) ∨ p4)))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802909829124601719779672705172 : (((p3 → (((p4 ∨ ((True ∨ p2) → ((((p3 ∧ (((p5 → p1) ∨ False) ∧ (False → p2))) ∨ (p2 ∧ p4)) ∧ True) → p1))) ∧ True) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111667674908216584614791653091 : ((((p4 ∨ ((p4 ∧ ((((p1 ∧ True) ∧ (False ∨ p4)) ∧ True) ∧ (p5 ∨ (((p3 → p4) ∧ True) ∧ p1)))) → p5)) ∨ False) ∨ p3) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601834840755764257303311839392 : ((((p4 ∧ ((((False ∨ ((p5 → ((p2 ∧ p3) → p1)) ∨ True)) → p1) ∨ p1) ∧ (((p4 ∨ ((p3 → p5) → p4)) → p2) ∨ p5))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254831882673681927813032273205 : ((p3 ∧ p5) → ((((p5 ∧ True) ∨ ((p5 → (p1 → p1)) ∧ ((p2 ∧ p5) ∨ (p4 → ((p5 ∨ p5) ∨ p1))))) → p4) ∨ (p2 → (True → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179105259585905250315399079600 : ((False ∧ ((p5 ∨ False) ∧ ((False ∨ (False ∧ (p3 ∨ (False ∧ p3)))) ∧ p2))) ∨ (False ∨ (p5 ∨ ((((p1 ∨ True) ∨ p4) → True) ∨ (p3 → p5))))) := by
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
theorem thm_5_vars_315039887598109458084310826370 : (p3 ∨ ((((p5 ∨ (p5 ∨ (True ∧ p3))) ∨ True) ∨ p3) → (((((p3 → (False → p5)) → p5) ∧ (((True ∧ p4) ∧ p2) ∧ False)) ∨ True) ∨ p1))) := by
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h7 =>
          -- Conjunctions on the left can always be decomposed.
          let h8 := h7.left
          let h9 := h7.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190119749637657376924492127940 : ((((p1 ∧ (p3 → True)) ∨ ((True ∨ p2) ∧ p3)) ∧ p1) ∨ (((((p3 ∧ False) ∧ (p2 → (p4 ∨ p1))) ∨ (False ∨ (p1 → p2))) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166283212033191927482047092782 : ((p4 ∧ (((False ∨ ((p2 ∧ p3) → ((((p1 ∨ False) ∨ p4) ∨ p5) ∨ p3))) → True) → False)) ∨ (True ∨ (((True ∨ (True ∨ p3)) ∧ p5) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221832410755135635429375055144 : (((p3 ∧ False) → p5) ∧ (((p3 ∨ ((p1 ∨ p4) ∨ p3)) → ((p4 → (p4 → (((p2 → p1) ∧ p4) ∨ (p3 ∧ p4)))) ∨ p1)) ∨ (False → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312472167174848232550540508449 : (p2 ∨ (p5 → (((((False ∨ (p5 → p3)) ∨ ((p1 → (True ∧ ((True ∧ (True ∧ p2)) ∨ p3))) ∨ p4)) → p1) ∨ (False ∨ (p4 ∨ p2))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_443429572287385263417392665474 : (((((p3 ∧ (True ∨ (((True → p3) → (p4 ∧ False)) ∨ p2))) ∨ ((p4 ∨ ((p5 ∧ p3) ∨ (p3 ∧ p4))) ∨ p1)) ∨ ((p4 ∧ p1) → p1)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192362317828002336299843341445 : (((p2 → ((False → (p1 ∨ p2)) ∨ (p1 → p3))) ∧ p3) → (p2 ∨ (((((((p1 → False) ∧ p1) ∨ True) → (p3 → p5)) → False) → p1) ∨ p3))) := by
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44674734568652495594006429276 : ((((((False ∨ p4) ∧ p5) ∧ (p1 ∧ p4)) → ((False ∧ (((p5 ∧ (p4 ∨ (True ∧ (p4 ∧ False)))) → p1) ∧ (p2 ∨ False))) ∨ p5)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54364627905685870125086435471 : (((p5 ∨ (False ∧ (p4 → ((p1 ∨ False) ∧ p3)))) ∧ ((p5 ∧ p5) → (((p3 ∨ p2) ∧ p4) ∨ ((False ∨ (p1 → p5)) ∨ (True ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217008447560092455751155049662 : ((((False ∧ p3) ∧ p4) ∨ p3) → (p2 → ((((((p3 → (p2 → (p5 ∧ False))) ∧ False) → p1) → (p5 ∧ p4)) ∨ ((p2 ∧ False) ∧ True)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49997881881374199514938285082 : (((((p1 ∨ (p3 → ((False ∨ False) → (p2 ∨ True)))) → p1) → (p2 ∧ ((True ∨ (False → p2)) → p3))) ∧ (((p5 ∧ p5) → p3) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233351223413193331650932930966 : ((True ∨ (p5 → p1)) → ((p1 → (True → p4)) → ((p4 → p3) ∨ ((p3 → p1) ∨ ((p5 ∧ ((p5 ∧ (False → p4)) → False)) → (p1 ∨ False)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (p5 ∧ (False → p4)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h5
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h7
    -- False on the left can always be used.
    apply False.elim h9
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h14 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h15 := h10 h14
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118590646135462102992662316441 : ((p4 ∨ ((p1 ∧ ((p4 → (p5 ∧ ((p2 ∧ (p4 → True)) ∧ (p1 ∨ ((p2 ∧ p5) ∨ p3))))) ∨ (False → (p3 → False)))) → p3)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244384397377193714109251784163 : ((False ∧ p1) ∨ (((True ∧ (True ∧ ((True → p5) ∧ ((p3 ∨ (True ∨ True)) ∨ p1)))) ∧ ((p5 ∧ (p2 → (p2 ∨ p3))) → False)) → (p5 → False))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h13 : (p5 ∧ (p2 → (p2 ∨ p3))) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h2
        -- Implications on the right can always be decomposed.
        intro h14
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h15 := h4 h13
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h18 : (p5 ∧ (p2 → (p2 ∨ p3))) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h2
          -- Implications on the right can always be decomposed.
          intro h19
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h19
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h20 := h4 h18
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h22 : (p5 ∧ (p2 → (p2 ∨ p3))) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h2
          -- Implications on the right can always be decomposed.
          intro h23
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h23
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h24 := h4 h22
        -- False on the left can always be used.
        apply False.elim h24
  case inr h25 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h26 : (p5 ∧ (p2 → (p2 ∨ p3))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Implications on the right can always be decomposed.
      intro h27
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h27
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h28 := h4 h26
    -- False on the left can always be used.
    apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149614033969674370164271134299 : ((p3 ∧ (p2 ∧ ((True ∧ p5) → ((((p1 ∧ True) ∧ (((p2 ∧ p1) → p5) ∨ (False ∨ p5))) ∨ p1) → p2)))) ∨ ((p4 ∨ True) → (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114526199470311044373598733850 : (((False ∨ ((((p4 → False) ∨ (p4 ∨ ((p5 ∨ p3) ∨ p4))) ∨ ((True ∨ p2) ∨ p5)) ∨ p3)) → (((p3 ∨ p3) ∨ p1) ∧ p2)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678042877132908537553473500540 : ((((((p2 ∨ (p4 ∨ (p4 → (p4 → p5)))) ∨ (p5 ∧ (p2 ∨ (p3 ∧ p2)))) ∨ (False ∨ (p2 ∨ False))) ∨ (((p3 ∧ p4) ∨ p1) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_31697646541061039184742312118 : ((False ∨ ((p3 ∨ (((((p4 ∨ (True → False)) ∧ (True → p5)) ∨ p3) ∨ (True → (p5 ∧ p3))) ∧ p4)) ∨ (p2 ∨ (True ∨ (p2 ∧ False))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_611528629266841910251393799243 : (((((p5 ∧ (((p5 → (p1 ∧ p3)) ∧ ((p5 ∨ p4) ∧ p4)) ∧ (((True → p1) ∨ (False → (p2 ∧ (p5 ∨ p3)))) → p3))) → p2) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_354675884926839458325551855205 : (p5 → ((((((((((p3 ∨ (p4 ∧ ((p4 ∧ p2) ∧ (p5 ∨ False)))) ∧ False) ∨ p2) → p2) ∧ p3) → p4) ∨ True) ∧ p1) ∧ (p1 ∧ p2)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49887507085221247137794458206 : ((((((p1 → p3) ∧ (((p2 ∨ p1) ∧ p5) ∧ p2)) ∧ ((p2 ∧ p5) ∨ (p5 → (p1 → p2)))) ∨ p3) ∧ ((p3 → False) ∨ (True → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190027273743705126469613933368 : ((((p4 ∨ ((True ∨ True) → (p4 ∨ p1))) ∧ p4) ∧ p4) ∨ (((False → (p2 → (p5 → ((True → False) ∨ p2)))) → (p3 ∨ False)) → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38208614671570428924180033461 : (((((p1 → ((True → (p2 → False)) ∧ ((p1 ∨ (True → (p1 ∧ False))) ∨ True))) ∨ ((p4 ∧ p2) ∧ False)) → ((p4 ∧ p5) → p2)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209160466838331914096188291417 : ((p3 ∨ (p3 ∧ ((False ∧ p1) ∨ p5))) → ((((p1 ∧ False) → (p5 → ((p1 ∧ p4) → p5))) → (True → p1)) ∨ (True → ((p5 → p5) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789954545350561060783079991616 : (((p5 ∨ ((True ∨ p4) ∧ (((((True ∧ p3) ∨ p5) ∧ True) → p4) ∨ (p5 ∨ (((True ∨ (p5 ∧ False)) ∧ True) ∧ ((p2 ∧ p2) ∨ True)))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208130585569875470791017408546 : ((((p1 → p3) ∨ p1) → (p4 → p5)) → ((p5 ∧ (p3 → ((p1 → (p1 ∨ False)) ∧ ((((p5 ∧ p4) ∧ True) ∨ p5) ∨ p2)))) → (p3 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54506386324332406308180219047 : ((((p2 ∨ (p1 ∧ p4)) ∨ ((p5 ∨ p1) ∨ p5)) ∨ ((False → p5) ∨ (p1 → ((p1 ∨ ((p5 ∨ p4) ∨ ((p4 ∧ p1) ∧ True))) ∧ p2)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160639416812177653650329753965 : (((True → (((p2 → p1) → p5) → ((False → False) ∨ p4))) ∨ (p1 → ((p2 ∨ (p3 ∧ p4)) ∧ p1))) → (p1 ∨ ((p5 ∨ (p4 → p4)) ∨ p2))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59312964005562935382553596247 : (((p4 ∨ p1) ∨ (((p4 → (p5 ∨ ((p1 ∨ p1) → False))) → (p5 ∧ ((p2 ∨ p1) ∧ p2))) → (p1 ∨ (((p1 ∨ p3) ∧ p1) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759177696860550132628400554666 : (((p2 ∧ (((True ∧ ((p5 ∨ (False ∨ (p1 ∨ (p1 ∧ (True → (p5 ∧ ((p3 → p3) ∧ p3))))))) ∧ p1)) ∧ (True → p1)) ∨ (p4 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337057572050068365394405977470 : (p1 → (((((p1 ∨ p4) ∨ (p4 → ((p2 → (p5 → (p4 ∨ (False → True)))) ∧ (((p4 → True) → p3) → p1)))) ∨ p5) → False) ∨ (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148091762781909738688208585273 : ((((((p3 ∨ (p3 ∧ p1)) ∨ p3) ∨ ((False → ((p4 ∧ (p2 → True)) ∨ p3)) → p5)) → p1) → (p2 → p4)) ∨ ((p4 ∨ (p3 ∨ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305928978684715843269198556644 : (p1 ∨ ((p5 ∨ (((p4 ∧ p5) ∧ True) ∨ p1)) → ((((p1 → p1) → p5) ∧ p1) ∨ (((False → p1) → p4) → (((False ∧ True) ∨ p4) → p4))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Implications on the right can always be decomposed.
      intro h16
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- False on the left can always be used.
        apply False.elim h18
      case inr h20 =>
        -- One of the premise coincides with the conclusion.
        exact h20
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- Implications on the right can always be decomposed.
      intro h23
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- False on the left can always be used.
        apply False.elim h25
      case inr h27 =>
        -- One of the premise coincides with the conclusion.
        exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136218900001987524276005520935 : ((((((False ∧ p5) ∨ p1) ∨ p3) ∨ False) ∨ ((True ∧ (p2 ∧ ((p2 → ((p4 → p3) → False)) ∧ p1))) → (p3 ∨ p1))) ∨ (False → (p1 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59099948497927010175701528504 : (((p5 ∧ p5) ∨ ((((p2 → p3) → False) → False) ∨ ((p1 ∧ (p2 → (p3 ∧ (p2 ∨ True)))) ∨ ((False → True) → ((p3 ∧ p2) → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112206519533915102812942557432 : (((False ∨ ((True ∧ (p5 ∧ ((p1 ∧ False) ∧ (((True → p2) → (((p1 ∧ (p5 ∧ p2)) ∨ p5) ∧ p5)) → False)))) ∧ p3)) ∨ p4) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198364857452885605102301664045 : ((p3 ∧ ((((p2 ∧ p2) ∧ p1) ∨ p5) ∧ p1)) ∨ (((p1 → (p3 ∧ p1)) ∨ (p1 ∧ p5)) → ((False ∨ (p4 ∨ (False → (p4 ∧ True)))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346769047397053388607900763749 : (p3 → (((p3 ∧ ((p2 → ((((p5 ∨ p4) ∧ p4) ∨ p3) ∧ True)) ∧ ((p5 ∧ False) ∨ (True ∨ p3)))) ∨ True) ∨ (p3 → (True → (p4 → False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789489542516031325421660261075 : (((p5 ∨ (((p3 → p1) → ((False ∨ (p3 ∨ True)) → ((p3 → True) ∨ p2))) → ((p1 ∧ ((p3 ∧ (p5 ∧ p2)) → (True ∨ p3))) → p1))) ∨ p5) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244468641197894183225387225996 : ((False ∧ p2) ∨ (True ∧ ((((p4 → (p4 → p1)) ∧ p5) → (True ∧ ((False ∧ p1) ∨ p5))) ∨ ((p1 → p1) → ((p2 → True) → (p5 → p1)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217003265344423445510780366864 : ((((True ∧ False) ∧ p5) ∨ p3) → (((((False → p2) ∧ ((p4 ∨ (p4 ∧ ((((p5 ∨ True) ∧ p2) → False) ∧ p3))) ∨ p2)) ∧ p2) → p5) ∨ p3)) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258849747201346053159833265758 : ((True → p1) → ((True ∧ (p4 ∧ ((True → (p4 ∨ p4)) ∧ p1))) ∨ ((p3 → p5) ∨ (p1 ∨ ((p3 ∨ ((p5 ∨ p2) ∧ (p5 ∨ p3))) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217356459576125869266233389514 : (((p3 ∨ (p1 ∧ p5)) ∨ p1) → (p1 → ((p3 ∨ (p1 → (((p4 ∨ p2) → ((False → p4) ∧ False)) → ((p3 ∨ False) ∧ (False → p3))))) ∨ True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597307388698439713197287709486 : (((((p1 ∨ ((p2 ∧ p2) ∧ p5)) ∧ (((p4 ∧ False) → p1) → (p5 ∧ (p5 ∧ ((p2 ∨ p4) ∨ (p4 ∨ ((p5 → p2) → p2))))))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654533985387781971284094927225 : (((((p5 ∧ ((((((p3 ∨ p1) ∧ p4) ∨ p1) ∧ ((p2 → ((p3 ∨ True) ∨ p5)) → p3)) → (False ∨ p1)) ∨ p3)) ∨ p4) ∨ (True ∨ p1)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_47385595511585747241167472041 : ((((p4 ∨ True) → ((((((((((False → p3) ∧ p5) ∧ False) ∧ False) → p3) → True) ∨ p1) ∧ p1) → (p5 ∧ p4)) ∧ True)) ∨ (False → p1)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149356768262130735365630928819 : (((p5 ∨ False) → ((((True → p3) ∨ p3) → (p2 → (p5 ∧ (p1 → True)))) → ((False ∧ (p3 ∧ True)) ∧ False))) ∨ (((p1 ∨ True) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608664073495209685102155685588 : (((((((((p1 ∨ p5) ∧ False) → True) → (((p2 ∧ (p5 → p4)) → (p4 ∧ p3)) → (p4 ∧ (p4 ∨ False)))) ∨ (p4 → p4)) ∨ True) ∨ p1) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_248333635232104021537358426383 : ((p2 ∨ p3) ∨ ((((p4 ∨ p1) ∧ ((p5 ∧ p5) ∨ (((p4 → True) ∧ ((p2 → p3) ∨ (p3 ∧ True))) → False))) ∧ p5) ∨ ((p3 → p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194094674024450094985428633454 : ((True → (p4 → ((p1 ∧ p5) ∧ ((p4 ∨ p5) ∧ False)))) → ((p5 ∧ p2) ∨ ((p3 ∧ (p4 ∨ (p5 ∧ (p1 ∨ (p2 ∨ (p2 ∧ p2)))))) → p5))) := by
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
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h6
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- One of the premise coincides with the conclusion.
        exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50644580580779731959594196561 : (((((((p5 → (False ∨ p5)) ∨ True) ∧ (True ∨ True)) ∨ True) ∧ (((p2 ∨ (p5 ∧ p2)) ∧ p5) ∨ False)) → (p4 ∨ ((p4 ∨ True) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313219214714046944478681133537 : (p3 ∨ ((((p2 ∧ p5) ∨ True) → (True ∧ (False ∨ (p3 ∨ ((p2 ∨ (((p5 ∧ p4) ∧ (p4 → (p4 ∨ False))) → p1)) ∨ (p3 → p2)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788890163142891961379992774437 : (((p5 ∨ ((True ∧ ((((True → (((p2 → p2) ∨ p2) ∧ True)) ∨ (p4 ∨ (((False → True) ∨ p3) ∨ p4))) ∧ p3) ∧ p3)) ∧ (p2 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675880096382895493160195853050 : (((((((p1 ∧ p3) ∨ (p5 ∧ p3)) → (p2 ∨ ((False ∨ True) → p3))) → (((False → True) → False) ∧ p4)) ∧ (((p5 ∧ True) ∧ p5) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622069278676053210381297265158 : ((((p2 ∧ ((p2 ∨ (((True → (p3 ∨ p5)) → ((p1 ∧ (p3 ∨ p2)) → (False ∧ p5))) → ((False → p1) → p4))) ∧ (p4 → p1))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_350913375084963240824936426086 : (p4 → (((p2 → ((p1 ∨ (p3 ∧ (((p4 → ((p3 ∨ p4) ∧ (p2 ∧ p3))) ∨ (p3 ∨ p5)) ∧ (False ∧ p3)))) ∧ p2)) ∧ p1) ∨ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218843514239250708222991561050 : ((p2 ∧ ((False ∧ p1) → p2)) → (((((True → (p1 ∨ (True ∨ False))) ∨ (p5 ∨ True)) ∨ ((p1 ∨ p2) ∨ p5)) → ((p1 ∨ p2) ∧ True)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307657329154068786596860258956 : (p1 ∨ (p1 → (p3 → ((p5 → p2) ∨ (((p5 ∨ p3) ∨ p3) → (((p2 ∧ ((p1 ∨ (p4 → p3)) → (p1 → p5))) ∧ (p2 ∧ p1)) ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
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
theorem thm_5_vars_65149452954825565566914292934 : ((p2 ∨ (p4 → (p5 ∧ (((p5 ∧ (p4 ∨ (p2 ∧ (p1 ∨ (p1 ∨ p3))))) ∨ (p3 ∧ (False ∨ (False → (p1 ∧ p1))))) → (p5 → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262518871819005257962425887660 : (True ∧ ((p5 → ((True → (True → ((p2 → (p1 ∨ p5)) → ((False ∨ p4) ∧ p2)))) ∧ ((p5 ∧ ((True ∧ True) ∨ (False ∧ p2))) → True))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134162433276539258243190281361 : ((((p3 → ((((p5 ∧ p5) → (p2 ∨ p2)) ∨ (True → p5)) ∨ ((p4 ∨ p3) → p4))) → ((p4 ∨ p4) ∧ p5)) ∨ False) ∨ ((False → p2) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159040589594855581012086816880 : ((p5 ∨ ((((p5 ∨ p3) → ((((p3 ∨ ((p1 → True) → False)) → p1) → p4) ∨ p2)) → p4) ∧ p1)) ∨ (p1 ∨ (True ∨ (p2 → (True ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184520727011260458335343974573 : (((p2 ∨ (p5 ∧ ((True ∧ p1) ∧ (p1 ∧ True)))) ∨ (p3 ∨ p5)) ∨ (((p1 ∨ ((False → (((p5 ∨ p2) ∨ False) ∨ p3)) ∨ p4)) ∨ p4) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180632948267594745865535930895 : ((((False → ((True ∧ True) → p2)) ∧ p2) ∨ (((p1 → p4) ∨ p5) → p5)) → ((p4 ∨ (((p1 ∧ p4) ∧ (p1 ∨ True)) ∧ (p2 ∧ p2))) → p4)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h3
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
    cases h12
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h10.left
      let h17 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h21 =>
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h10.left
      let h24 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h28 =>
        -- One of the premise coincides with the conclusion.
        exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234336121761257955000906217325 : ((p1 → (p5 ∧ p2)) → ((p4 ∧ p2) → (p2 → (p5 ∨ (((p2 ∨ p4) ∨ ((p1 → (True ∧ (((True ∨ p5) ∨ p5) ∨ False))) ∨ p3)) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190128922259023789704387210347 : ((((True → (p4 ∧ p3)) → ((p3 ∧ p3) → p2)) ∧ p2) ∨ (((p3 ∨ (p2 → False)) ∨ (p2 ∨ True)) ∧ (p2 ∨ ((p5 → False) → (False → False))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112145202312719258652767200441 : (((p1 ∧ (((p3 ∨ (p5 ∨ p1)) → ((p3 ∧ p3) ∧ p4)) ∧ (((((p2 → p2) ∨ p3) ∧ True) ∨ p5) ∨ (p3 ∨ p3)))) ∨ p5) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134673405936698031319044161360 : (((((p3 ∨ (p1 ∧ p2)) ∨ (True ∨ (True ∧ p3))) ∨ (((p1 → False) ∨ p2) → ((True ∨ True) ∨ (p2 ∧ p5)))) → p1) ∨ ((p5 → True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230086494878359655291515741051 : (((p2 ∧ p5) ∧ p4) → (((((p1 ∨ (False → p1)) ∧ p5) ∧ p2) → (p3 ∨ p5)) → (((p2 → False) → ((p3 ∨ (p3 → p1)) ∨ p3)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h8 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_97732075659544131037358634771 : ((p3 ∨ (((False → False) → (False ∧ ((True ∨ (p1 ∧ False)) ∧ p2))) ∧ ((((p4 → (p3 → p1)) ∧ (p4 ∨ True)) → p4) ∨ (p4 → True)))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h7 : (False → False) := by
        -- Implications on the right can always be decomposed.
        intro h8
        -- False on the left can always be used.
        apply False.elim h8
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h9 := h4 h7
      -- We need to get the left conjuct of h9 based on <expert-advice>.
      let h10 := h9.left
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h12 : (False → False) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- False on the left can always be used.
        apply False.elim h13
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h14 := h4 h12
      -- We need to get the left conjuct of h14 based on <expert-advice>.
      let h15 := h14.left
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148566573609846512571848866264 : (((p1 ∧ (True → (p3 ∨ (p1 ∨ ((p4 ∨ p1) → p4))))) ∧ ((p5 ∨ True) → (((False → p1) ∧ p1) ∧ p2))) ∨ (False → (False ∧ (p2 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346803212580077856930183000256 : (p3 → ((p5 ∨ ((p3 → p5) ∧ (((((p2 → p4) ∧ True) ∧ (False ∧ False)) ∨ (p1 → (p3 → p3))) → p1))) ∨ ((p2 ∨ (p3 → True)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177971413964208215531217440945 : (((True ∧ ((p5 ∨ (p4 ∨ ((True ∧ p1) ∧ (p3 → True)))) ∧ p1)) ∨ p2) ∨ ((True ∧ (p4 ∧ p1)) ∨ ((p2 ∧ p2) → ((True ∨ p2) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164536933574219720481518731197 : (((((False → (p3 ∨ ((True ∨ p4) ∧ (p3 ∧ p2)))) → p5) → (p2 ∨ (p2 ∨ False))) ∧ p2) ∨ (False → ((p3 ∧ p5) ∧ ((p1 ∨ p4) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135080746535834188287213433236 : ((((((p4 ∨ (p1 ∧ (p1 ∧ p3))) ∧ False) ∧ (((p2 ∧ True) ∧ p1) ∨ p5)) ∨ (p2 ∨ (p4 → p4))) ∨ (p5 ∧ p5)) ∨ ((p3 → p1) ∧ True)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178481446123164034949923746975 : ((((((p4 ∧ p4) ∨ p5) ∧ p5) ∧ (True ∧ p5)) ∨ (p1 ∨ (p5 → True))) ∨ ((p5 → ((((p1 ∨ p3) → p3) ∨ p3) → True)) ∨ (p5 ∨ p3))) := by
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
theorem thm_5_vars_114892664003363510976781186992 : (((p1 ∨ ((((p1 ∧ False) ∨ p1) → p3) → ((p3 ∧ p1) ∨ (p3 → True)))) ∨ (p5 ∨ ((p1 ∨ (True ∧ (True ∨ p5))) → False))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53396943687363403532059017758 : ((((p3 ∧ (True ∨ ((p4 → (True ∧ True)) ∨ p2))) ∧ (p1 → p4)) → (True ∧ (((p5 ∨ (p3 → True)) ∧ p3) ∧ (p1 → (True → p4))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
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
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h13.left
  let h16 := h13.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h17 =>
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h20 =>
      -- One of the premise coincides with the conclusion.
      exact h15
  -- Implications on the right can always be decomposed.
  intro h21
  -- Implications on the right can always be decomposed.
  intro h22
  -- Conjunctions on the left can always be decomposed.
  let h23 := h1.left
  let h24 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h25 := h23.left
  let h26 := h23.right
  -- Disjunctions on the left can always be decomposed.
  cases h26
  case inl h27 =>
    -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
    have h28 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h21
    -- We have shown the premise of h24, we can now drive its conclusion.
    let h29 := h24 h28
    -- One of the premise coincides with the conclusion.
    exact h29
  case inr h30 =>
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h31 =>
      -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
      have h32 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h24, we can now drive its conclusion.
      let h33 := h24 h32
      -- One of the premise coincides with the conclusion.
      exact h33
    case inr h34 =>
      -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
      have h35 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h24, we can now drive its conclusion.
      let h36 := h24 h35
      -- One of the premise coincides with the conclusion.
      exact h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234856220022512176872078393052 : ((p5 → (False → True)) → ((((p1 → p1) → p5) ∨ (True ∨ (p1 ∧ ((False ∨ False) ∧ (True ∧ (p2 → (((p3 ∧ p3) → p1) ∨ p4))))))) ∨ p2)) := by
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
theorem thm_5_vars_708815388713996785968467709905 : (((((p3 → (p5 → (p3 → (p3 ∨ True)))) → p5) → (((((((p1 ∨ p5) ∧ p4) → p5) ∨ (p2 ∨ (p2 ∨ True))) ∨ p4) ∧ p2) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167595834188435870757173798038 : (((p4 ∧ (((p5 ∨ p1) → p1) ∨ (((p4 → p1) ∨ p1) ∧ (p3 → True)))) ∨ (p5 ∧ p2)) → (((p3 ∧ p4) ∨ (p2 → (True ∨ p1))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Implications on the right can always be decomposed.
      intro h6
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
        -- Implications on the right can always be decomposed.
        intro h11
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h17
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651313687069636006449949894517 : ((((((p4 ∧ p5) ∧ p4) ∨ (False → (p4 → ((((((p2 ∨ p1) ∨ p1) → (False → (p1 ∨ p4))) ∨ p1) ∧ p5) ∨ p3)))) ∧ (p4 ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42305378202871322629361489146 : (((p2 ∧ (((p1 ∧ ((p1 → ((p3 → p3) ∨ (p4 ∧ p4))) → ((p2 → p4) ∨ p2))) → False) ∨ (((p2 ∨ p2) ∨ True) ∧ p2))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139226898342097910344072889159 : ((((p4 → (p3 ∨ True)) → (((((p5 ∧ p4) → True) ∧ p5) ∨ p3) → (p2 ∨ ((p5 ∧ p2) ∧ (p5 ∨ p2))))) ∨ False) → ((p2 → p4) ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210216758098121130021872043782 : ((((True ∧ p5) → p5) ∨ p2) ∧ (p4 ∨ ((((False ∧ p5) ∧ (p2 → p4)) ∨ ((((True ∨ False) ∧ (p1 ∧ (p3 → p3))) ∧ True) ∧ True)) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249458466612132633902171401982 : ((p5 ∨ False) ∨ (p4 ∨ (True → (((p1 → (p4 ∨ p4)) ∧ (p5 ∨ p4)) → (False ∨ (((p4 ∧ p2) ∧ True) → (False → ((p4 ∧ p1) → p5)))))))) := by
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
  cases h4
  case inl h5 =>
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
    -- False on the left can always be used.
    apply False.elim h7
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205118740431526401810142159079 : ((((p5 ∨ p4) ∨ True) ∧ (p1 ∧ False)) ∨ ((((((p2 ∧ False) → (p4 → (True → True))) → p5) ∧ False) ∨ (p2 → (p1 ∨ True))) ∨ (p1 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



