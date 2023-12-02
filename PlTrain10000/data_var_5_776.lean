variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83943308823377659946585857605 : (((p5 ∨ (p3 ∨ ((((p4 ∧ p2) ∨ (((p2 → True) ∧ False) → p3)) ∨ p5) ∨ (False → p2)))) → ((p4 ∨ (p1 → (p3 → True))) → False)) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ (p3 ∨ ((((p4 ∧ p2) ∨ (((p2 → True) ∧ False) → p3)) ∨ p5) ∨ (False → p2)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p4 ∨ (p1 → (p3 → True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h5
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42536338126321062801314477857 : (((p1 ∨ (((((p5 ∨ (False → False)) ∧ (((False ∧ (p5 → (p1 ∨ p1))) ∨ p5) → p2)) ∧ (p2 → p4)) → False) ∧ (p5 ∧ p4))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317717150220058797298321660555 : (p4 ∨ ((((((p2 ∧ (p2 ∧ ((False ∨ (True ∨ p5)) ∨ (True ∨ (p2 ∧ p3))))) → (p4 ∧ False)) ∧ True) → (p2 ∨ p1)) → (p2 ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299344885295562246307953282549 : (False ∨ ((((p2 ∧ p5) → p3) ∨ ((p4 → (((p1 ∧ (((((p3 → (False ∧ False)) → p5) → p1) ∨ p1) ∧ p4)) ∨ p3) ∨ p4)) ∨ p2)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64949680206654752306367162565 : ((p2 ∨ ((((False ∧ (((False ∧ p3) ∧ p5) → p4)) ∨ p2) ∧ p5) → ((((False → (p5 ∧ True)) → (p4 → p1)) ∧ (p5 ∨ p2)) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57763301663245059540192681873 : ((((p4 → p2) → p3) → (((False ∧ (p4 ∨ p2)) ∧ (((p4 ∨ False) ∨ p5) → (((p1 → p5) ∧ False) ∨ False))) ∨ (p5 → (p5 ∧ True)))) ∨ p4) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60137471701009209097640111895 : (((p4 ∨ p1) → ((p1 → ((((p1 ∨ p4) → p5) ∧ (False ∨ p4)) ∧ (((p5 ∧ p2) ∧ (p4 ∧ ((p4 → p3) ∧ False))) ∨ False))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186910525595336747556714363942 : ((((p3 ∨ True) ∨ p4) ∧ (p2 ∧ ((p2 ∨ p5) ∨ (p5 → p2)))) → (((False → p4) ∨ ((p4 → p5) ∧ p1)) ∧ (p4 → (p5 ∨ (p4 ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h3.left
      let h7 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h10
          -- False on the left can always be used.
          apply False.elim h10
        case inr h11 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h12
          -- False on the left can always be used.
          apply False.elim h12
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h14
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h3.left
      let h17 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h20
          -- False on the left can always be used.
          apply False.elim h20
        case inr h21 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h22
          -- False on the left can always be used.
          apply False.elim h22
      case inr h23 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h24
        -- False on the left can always be used.
        apply False.elim h24
  case inr h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h3.left
    let h27 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h30
        -- False on the left can always be used.
        apply False.elim h30
      case inr h31 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h32
        -- False on the left can always be used.
        apply False.elim h32
    case inr h33 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h34
      -- False on the left can always be used.
      apply False.elim h34
  -- Implications on the right can always be decomposed.
  intro h35
  -- Conjunctions on the left can always be decomposed.
  let h36 := h1.left
  let h37 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h36
  case inl h38 =>
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h39 =>
      -- Conjunctions on the left can always be decomposed.
      let h40 := h37.left
      let h41 := h37.right
      -- Disjunctions on the left can always be decomposed.
      cases h41
      case inl h42 =>
        -- Disjunctions on the left can always be decomposed.
        cases h42
        case inl h43 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h35
          -- One of the premise coincides with the conclusion.
          exact h43
        case inr h44 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h44
      case inr h45 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h35
        -- One of the premise coincides with the conclusion.
        exact h40
    case inr h46 =>
      -- Conjunctions on the left can always be decomposed.
      let h47 := h37.left
      let h48 := h37.right
      -- Disjunctions on the left can always be decomposed.
      cases h48
      case inl h49 =>
        -- Disjunctions on the left can always be decomposed.
        cases h49
        case inl h50 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h35
          -- One of the premise coincides with the conclusion.
          exact h50
        case inr h51 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h51
      case inr h52 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h35
        -- One of the premise coincides with the conclusion.
        exact h47
  case inr h53 =>
    -- Conjunctions on the left can always be decomposed.
    let h54 := h37.left
    let h55 := h37.right
    -- Disjunctions on the left can always be decomposed.
    cases h55
    case inl h56 =>
      -- Disjunctions on the left can always be decomposed.
      cases h56
      case inl h57 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h53
        -- One of the premise coincides with the conclusion.
        exact h57
      case inr h58 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h58
    case inr h59 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h53
      -- One of the premise coincides with the conclusion.
      exact h54



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121388240257990626048068475156 : ((((((p1 ∧ p3) → (False ∨ ((p2 ∨ ((p3 → p2) → True)) ∧ p1))) ∧ (((False ∧ False) → p5) → (p3 → False))) ∨ p5) → p1) → (p5 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137436389025863313231278054292 : ((p4 ∧ ((False ∨ ((p1 ∧ (p2 → p1)) → (True ∨ (True ∨ ((p2 → (p3 ∧ p1)) → p3))))) ∧ (p4 ∧ (p3 → False)))) ∨ (p1 ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20184412645649348102761585110 : ((((((((p2 → (p1 ∧ (p5 → p2))) → True) → False) ∧ p2) → True) → p3) ∨ (p1 ∨ (p2 → (False ∨ (p4 ∨ ((p3 ∨ p2) ∨ True)))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314644529904405004800040894437 : (p3 ∨ ((((p2 → ((p4 → p2) → ((((False → p3) ∨ True) ∧ p4) ∨ False))) ∧ p3) → False) ∨ (True → ((p2 ∧ (False ∧ (p5 ∧ False))) → p3)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317994461380857253484328387390 : (p4 ∨ ((p5 → (((p4 ∧ p3) ∨ ((p4 → p1) ∨ (p3 ∨ ((((p5 → ((p5 ∨ True) ∧ p5)) ∧ False) ∧ p4) → p3)))) ∧ (False ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328540549694704215844060125880 : (True → (((((p2 ∨ (p4 → ((p5 ∧ p1) → True))) ∧ (p1 → p2)) ∨ (p5 ∨ p3)) ∧ True) → (((False ∨ (p4 ∨ (p3 ∨ False))) ∧ True) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164594916675376598479579450415 : ((((p1 ∧ True) → ((((False ∧ p5) ∧ (p3 ∧ p2)) → (p3 ∧ p5)) → (p1 → p3))) ∧ p5) ∨ (((p5 ∧ p4) → (p4 ∧ (p2 ∨ p5))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66379104903263273441098646839 : ((p5 ∨ (p3 ∨ ((p4 ∨ False) ∨ ((p4 ∧ (((True ∧ ((False ∧ (p5 ∨ p4)) → p1)) ∨ p3) → False)) → (p2 ∧ ((p3 ∨ True) ∧ False)))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((True ∧ ((False ∧ (p5 ∨ p4)) → p1)) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h4
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h13 : ((True ∧ ((False ∧ (p5 ∨ p4)) → p1)) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- False on the left can always be used.
    apply False.elim h15
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h17 := h12 h13
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122671899976730037653558545658 : (((((p4 → ((True → (p2 ∨ False)) ∨ False)) ∨ (True → (p3 ∧ p5))) ∨ (((p4 ∨ p1) → (p3 ∧ p5)) → False)) → (p2 → p2)) → (p5 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110879180900844481300394539058 : (((((p1 ∨ ((True → ((False ∨ p2) ∨ (False ∧ (p5 ∨ ((p5 ∧ p5) ∨ False))))) ∨ p4)) ∧ ((p2 ∧ p3) ∧ p1)) → False) ∧ p2) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758938365186342128465159521914 : (((p2 ∧ (((p4 → ((p5 → (((False → True) → p2) → p4)) ∨ p1)) ∧ ((p2 ∨ ((p3 ∧ p5) → p4)) → (p1 ∨ (False → p1)))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252407099315924436429478872191 : ((p5 → False) ∨ ((False ∨ (p3 ∨ ((False ∧ (((False ∨ p1) ∨ (p5 → p5)) → (p1 → p3))) ∨ p3))) ∨ ((p4 ∨ (True ∨ p3)) → (p1 → True)))) := by
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
theorem thm_5_vars_113992168829340357943830376839 : (((p1 → ((((p2 ∨ False) → (p1 ∧ p5)) ∨ (p5 ∨ ((p2 → (p3 ∧ (p2 → p5))) → False))) ∨ p2)) ∧ (False ∧ (p1 → p2))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321618795140467244478992494362 : (p4 ∨ (p3 → (((p2 ∨ (p2 ∨ True)) ∧ ((True ∨ (p4 ∧ p1)) ∧ (False ∨ p1))) ∨ ((p2 ∨ True) ∧ (True ∨ (p3 → (False ∧ (p2 ∨ p3)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_316624888549530532173099242998 : (p3 ∨ (p4 ∨ ((p3 ∨ ((p5 → p3) → (p4 ∨ ((p3 ∨ ((False ∨ (p5 ∨ False)) ∧ True)) ∨ (True ∨ (p2 ∧ False)))))) ∨ ((p5 ∨ p5) ∨ p1)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317049339336878896317053161052 : (p3 ∨ (p4 → ((((p1 ∧ (((True ∧ (p5 → p1)) ∨ (p5 ∨ (True → p2))) ∨ p3)) → ((p1 ∨ p4) ∧ p5)) ∨ p3) ∨ ((True ∨ p1) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_256723882580612216049819627834 : ((p1 ∨ p1) → ((p3 → ((False ∧ p3) → ((p3 ∨ False) → False))) ∧ (((p2 ∨ p3) ∧ True) ∨ (False ∨ ((False ∧ p5) → ((p2 ∨ True) ∧ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
    -- Conjunctions on the left can always be decomposed.
    let h13 := h10.left
    let h14 := h10.right
    -- False on the left can always be used.
    apply False.elim h13
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- False on the left can always be used.
    apply False.elim h17
    -- Conjunctions on the left can always be decomposed.
    let h19 := h16.left
    let h20 := h16.right
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110474332061423713293660391649 : ((p4 → (((p2 ∧ ((((p4 ∨ True) ∧ p2) → (p5 ∨ ((((False → p3) ∨ p1) ∨ False) → p1))) ∨ True)) ∨ (True ∨ True)) ∨ p5)) ∧ (p2 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232746129238771151200476342125 : ((p1 ∧ (p2 → p4)) → (((p5 ∧ (False ∧ (((False ∨ True) → p3) → p1))) ∧ (True ∧ (p2 ∨ ((p2 ∨ p4) ∨ True)))) ∨ (True ∨ (False ∧ p5)))) := by
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
theorem thm_5_vars_134324892079086327596799706276 : (((p2 ∧ (((((((p1 ∨ True) ∧ (True → p1)) → (p1 ∨ p2)) ∧ p4) ∨ ((p2 ∨ p5) ∧ p3)) ∨ False) → p3)) ∨ p5) ∨ ((True ∧ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261404262484201961277852911961 : ((p5 → p1) → ((p4 ∧ (p1 ∨ (False ∨ p1))) → (((p4 ∧ p3) ∨ (p1 → (p2 → True))) → (p4 → (((p1 ∧ p2) → (p3 ∧ False)) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h2.left
    let h9 := h2.right
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
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h2.left
    let h16 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670228583941935360712915426700 : ((((((p1 → p2) ∧ (p5 ∧ p4)) ∨ (True → (True ∧ (((p4 ∨ p2) → ((False ∧ p3) ∧ p4)) ∨ (p1 → p1))))) ∨ (False → (p2 ∧ p5))) ∨ False) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696277761805977274979941031363 : ((((False → ((((p2 → ((False ∧ (p2 ∧ p2)) ∧ p2)) ∧ p3) ∧ p3) → p1)) → (((p3 ∨ p1) → (p1 ∧ True)) ∧ (False ∨ (p4 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710289604782827975520678085750 : (((((True → ((p5 ∧ False) ∨ p1)) ∨ True) ∧ (((((p3 ∧ p4) → p3) ∧ ((p4 ∧ p4) ∨ p4)) ∨ (False → (p3 → p4))) ∨ (True → True))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229672504264865016122427945670 : ((p3 → (p2 → False)) ∨ (((((True → False) ∨ p1) ∧ True) ∨ (((p5 ∨ ((p3 ∨ p2) ∧ ((p3 ∧ False) ∨ True))) → (p3 ∧ p5)) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121828207110056131311244108928 : ((((True ∧ p1) ∨ (((True ∧ (p4 ∨ (False ∨ True))) ∨ (p3 ∨ (((p5 ∧ False) → p3) ∧ p4))) ∨ (p3 ∨ (True → p1)))) → False) → (p3 ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∧ p1) ∨ (((True ∧ (p4 ∨ (False ∨ True))) ∨ (p3 ∨ (((p5 ∧ False) → p3) ∧ p4))) ∨ (p3 ∨ (True → p1)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : ((True ∧ p1) ∨ (((True ∧ (p4 ∨ (False ∨ True))) ∨ (p3 ∨ (((p5 ∧ False) → p3) ∧ p4))) ∨ (p3 ∨ (True → p1)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_442686281067946195344577447025 : (((((p2 ∧ (((((p3 ∨ True) → (((((p4 ∨ p4) → p5) → p5) ∧ p5) ∧ p4)) ∨ False) ∧ p1) ∧ p5)) → False) ∨ (True ∨ (p2 → p4))) ∧ True) ∧ True) := by
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
theorem thm_5_vars_76530430949252608197269581369 : ((((((False ∨ p4) → p1) ∨ ((p4 ∨ ((p3 ∧ (p2 ∧ (p3 ∧ p2))) ∨ p3)) ∨ (p5 → (False ∧ p3)))) → ((True → p5) ∨ True)) → False) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((False ∨ p4) → p1) ∨ ((p4 ∨ ((p3 ∧ (p2 ∧ (p3 ∧ p2))) ∨ p3)) ∨ (p5 → (False ∧ p3)))) → ((True → p5) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
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
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h9 =>
            -- Conjunctions on the left can always be decomposed.
            let h10 := h9.left
            let h11 := h9.right
            -- Conjunctions on the left can always be decomposed.
            let h12 := h11.left
            let h13 := h11.right
            -- Conjunctions on the left can always be decomposed.
            let h14 := h13.left
            let h15 := h13.right
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h18 := h1 h2
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300779503965231721716677020610 : (False ∨ ((((p4 ∨ (p2 ∨ ((p2 ∨ (False ∨ p5)) ∨ (p2 → False)))) → p4) ∨ (False ∨ p4)) ∨ (((p2 ∧ p2) → (True ∨ p2)) ∨ (True ∧ False)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135787877945772671737967282760 : ((((((True ∨ True) ∧ p1) ∨ (True → p4)) ∨ ((p5 ∧ (p1 ∧ p4)) → True)) → ((p2 ∨ p3) ∨ (p1 ∨ (p4 ∧ p1)))) ∨ (p5 → (p5 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340880633334152974707976308780 : (p2 → (((((p2 ∧ (((p3 → True) ∨ p5) ∨ p5)) → True) → ((p4 ∧ (False ∧ p4)) → p5)) → (((True → (p4 → False)) → False) ∨ p2)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315054586504670802433362524493 : (p3 ∨ (((True ∧ p3) ∨ (p3 ∨ (p4 → (False ∨ False)))) → (((False ∨ (True ∧ (p1 → (p2 → p5)))) → (p5 ∧ p5)) ∨ (p3 → (False → p1))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
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
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341998604037920195205624884264 : (p2 → ((((p5 ∨ p4) → True) ∧ (p3 ∨ (p3 ∧ ((p5 ∧ True) ∨ (p4 ∧ (((True ∧ (p5 ∧ p5)) ∧ p2) ∧ p5)))))) ∨ (p2 ∨ (p5 ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337520473817177424530322207705 : (p1 → ((((((p4 → ((p4 ∨ (p1 ∧ (((p5 ∧ True) ∨ True) ∨ p2))) → p5)) → False) → p4) → p5) ∨ p5) ∨ (p2 → ((p3 → p1) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147967238487834728154901367556 : (((True → ((p3 ∨ p2) ∧ (p3 → (p2 ∨ (((p3 ∨ ((p3 → p1) ∨ p3)) → p4) ∧ False))))) ∧ (p2 → p4)) ∨ ((p4 → (p3 → True)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_913871298754852317221966700559 : (((((p5 ∧ (True → ((p3 ∨ (p2 ∧ ((p3 → p4) → (p5 → p4)))) ∧ False))) ∧ True) ∧ (p5 → ((True ∧ (True → (p4 ∨ p1))) ∨ p2))) → p3) ∧ True) := by
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
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67777820126246372532914411971 : ((p2 → ((p5 ∧ ((p4 → (True → ((((p4 → (((p1 → (p2 ∨ p4)) → False) ∧ p5)) ∨ True) ∨ (p2 → p5)) ∧ p1))) → p1)) ∨ p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52242356554231778912846998724 : (((p5 ∧ (((((p1 → (True ∧ (p1 ∨ True))) → p5) ∨ p1) ∨ (True → False)) → p2)) → (p1 ∧ ((True → p3) → ((p4 → False) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40249965535003841955396512100 : ((((False ∨ ((((True ∧ ((False ∨ p1) ∨ True)) → (p4 → p1)) ∧ ((False ∨ ((p5 ∨ (False → True)) ∨ p1)) ∧ True)) ∨ p5)) ∧ p5) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665446466959079186895220998900 : ((((((((((((False → p1) → False) → p3) ∧ True) ∧ p2) ∨ (((p1 ∨ p3) ∧ p4) ∨ p1)) → p1) ∧ p1) ∨ p5) ∧ ((False ∧ p5) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156223596716732801190005951527 : ((p3 ∨ (((p3 ∨ p4) ∧ ((p3 ∧ ((False ∧ True) ∧ ((p5 ∧ p2) → (p3 ∨ True)))) ∧ p2)) ∨ True)) ∧ (False → (p5 → (p4 ∨ (p3 ∨ p3))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232446033775536898122570269994 : ((True ∧ (p5 ∧ p1)) → (p5 ∧ ((((p5 ∨ p4) ∧ (p2 ∨ (((False ∧ True) ∧ p1) ∨ p4))) ∨ ((p4 ∨ (False ∨ p2)) ∨ p2)) ∨ (False ∨ p5)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764137782334230284475473013644 : (((p3 ∧ (p4 → ((((((p4 → ((p3 ∧ True) → p4)) → False) ∧ (p1 → (p3 → p5))) → p3) ∨ (p5 ∧ p1)) ∧ ((p5 ∨ p2) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164543661275079233178543078038 : (((((p2 ∧ (((p4 ∧ p2) → True) ∨ True)) ∨ p3) ∨ (p5 ∧ (p3 → (p2 → p4)))) ∧ p1) ∨ (p2 → ((p4 ∨ (False ∨ (p2 ∨ p5))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160563324478652494736262947690 : (((((False ∨ p4) → ((p1 ∧ (p3 ∧ p1)) ∧ False)) ∨ (p4 ∨ p3)) → (p3 → ((p3 ∨ p3) ∧ p5))) → ((p1 ∨ (False → p5)) → (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344290194872338991956349776480 : (p2 → (p3 ∨ ((p2 → (p4 ∨ ((((True → p5) ∧ p4) ∧ (False → (p3 ∧ (p5 → p1)))) → ((p5 → p1) ∨ ((True ∨ p5) ∨ p4))))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612023737960924957050136525373 : ((((((((((p3 ∧ (p4 → ((True → True) → True))) ∨ False) ∧ (p4 ∧ p5)) → p4) → (p1 → (False ∧ p1))) → p5) ∧ (p3 → p4)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113261086539457837956311013243 : (((((True ∧ ((False ∧ (((p4 ∨ False) ∨ p1) → p5)) → (p5 ∧ p4))) → (p2 ∧ p1)) ∧ ((p4 → p5) ∨ p4)) ∧ (p1 → p3)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345159119946430145300949328405 : (p3 → (((p4 ∨ (p1 ∧ p2)) → ((((p4 ∧ (((True → ((p5 ∨ False) → (p1 ∧ p4))) ∧ True) ∧ p1)) → p2) ∧ p2) ∨ (p3 ∧ p3))) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- One of the premise coincides with the conclusion.
    exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51236609132759924539830527818 : (((((p4 ∨ True) → p1) ∧ (p3 ∧ (False ∧ (((p5 ∧ p5) ∧ p4) ∨ (p4 → (p2 ∨ False)))))) ∨ (True ∧ (p2 ∧ ((p2 ∧ p1) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179619299947314804930884535641 : ((p4 → ((p1 ∨ (((((p3 ∨ p1) ∨ p2) ∨ False) ∧ p1) ∨ p2)) ∨ p2)) ∨ ((p1 ∧ (((((p2 ∨ p5) → p3) → p1) → p1) ∨ False)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785252434270424974457131376618 : (((p4 ∨ ((p4 ∧ (p3 ∨ (p3 ∨ (False ∨ ((p2 → p3) → ((((True → p2) ∧ (p1 ∧ p1)) ∨ p1) ∧ ((p2 → True) → p3))))))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345356686692726439098819018505 : (p3 → ((((((True ∨ False) → (p4 → False)) ∧ (((p2 ∨ (p5 ∨ (False → (p5 → p1)))) ∨ (p4 → (False ∨ p3))) → p4)) ∨ p5) ∨ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57743879039742138173763741517 : ((((True → False) → p3) → ((p3 ∨ (((p5 → (p2 → p4)) ∧ p4) ∧ ((p2 ∧ (True → False)) ∧ ((True ∨ p3) ∨ False)))) ∨ (p3 → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200700128909623898919962987522 : ((p2 ∧ ((p2 → (p4 ∧ p3)) → (p1 → p4))) → ((((False → p3) ∧ ((p4 → p1) ∨ (False → (p4 → p3)))) ∨ p5) ∧ ((p3 → p3) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50428052377476633850358135747 : (((p4 ∧ (p4 ∧ (((((((p1 → p3) ∧ p2) ∧ p4) ∨ p3) ∧ True) ∨ (True ∧ p3)) ∨ (p3 ∨ p4)))) ∨ ((p4 ∨ (True ∧ True)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204744463122981118731347665754 : (((p4 → ((p3 ∧ p3) ∨ p5)) ∨ p3) ∨ (p5 ∨ (((True ∨ (p3 ∧ (p2 → p2))) ∨ False) → ((p2 ∧ False) ∨ (False → (p3 ∨ (p5 ∨ True))))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351248471822929118335866203856 : (p4 → (((p5 ∨ p1) ∧ (p3 → (p3 → (((p1 ∨ ((True ∨ (p2 → (True ∨ (p2 → p1)))) ∨ p3)) ∨ True) → p5)))) ∨ ((p5 → False) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180087319866625814278960901325 : (((((((p4 → p2) ∨ (True ∧ True)) → (p2 ∨ p1)) → False) ∧ True) → p4) → (p2 ∨ (p2 ∨ (((((p3 → False) ∨ p2) → p3) ∧ p5) → True)))) := by
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
theorem thm_5_vars_46977834053754955379374660858 : (((((p1 → (((p5 → (p2 → True)) ∨ p1) ∨ (False ∨ (((p1 → (True → True)) ∧ p1) → p5)))) ∧ (p4 ∨ False)) → p5) ∨ (True ∨ p2)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610856493068268122937732474906 : (((((((p1 ∨ (p3 ∨ ((True → (True → (p2 ∧ False))) ∨ True))) ∨ (p5 ∨ p4)) → (((p5 → (p5 ∧ p5)) ∨ p3) ∨ False)) → p4) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_114657430136711895067830230406 : (((((p3 → p3) ∧ ((p5 → p1) ∨ p4)) → (((p1 ∨ (p3 → False)) → p2) → p2)) ∨ ((p5 ∧ p5) → ((p4 ∨ p4) → p5))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319471655332189219466688381929 : (p4 ∨ ((True → (p1 ∧ (False ∧ (((p3 ∨ (True ∧ p2)) ∨ p2) ∧ p2)))) ∨ ((p5 ∧ p5) ∨ ((p4 → p1) ∨ ((p5 ∧ p2) → (p4 → p5)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215222394301103547570305925517 : ((False ∧ ((p2 ∨ p3) ∧ p3)) ∨ (p4 ∨ ((((p3 ∨ (p1 ∨ p3)) ∨ (False ∨ (True → True))) ∨ (((p2 ∧ False) → False) ∧ (p4 ∨ p2))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258998393704318037603679944186 : ((True → p3) → (p4 → ((p1 → ((False ∧ False) → False)) → ((((((p4 → ((p5 ∧ (p4 ∨ True)) → False)) ∧ False) ∧ p5) ∨ True) ∨ p3) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158540716254378822846445282096 : (((p2 → p1) → (True ∧ (p4 ∧ ((((p2 → p2) ∧ ((True ∧ p5) → (p4 ∧ False))) → p5) → p1)))) ∨ ((p3 ∧ False) → (p3 ∨ (False ∨ False)))) := by
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
theorem thm_5_vars_190031964566309419025874864502 : ((((((p5 ∧ (p5 ∨ p4)) → p4) ∧ p2) ∨ p5) ∧ True) ∨ (p2 ∨ (p4 ∨ ((False ∧ ((False → (((p5 ∧ p4) ∨ p4) ∧ p2)) ∧ p5)) → p4)))) := by
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
theorem thm_5_vars_51845196520053506010314710089 : ((((((p4 ∨ p2) → (p5 ∨ (True → p3))) ∧ (((p4 ∨ p4) ∧ False) ∨ p2)) ∧ p3) ∨ ((p3 ∨ (p1 ∨ (True ∨ p4))) → (p5 ∨ True))) ∨ False) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249871631318130981202078406370 : ((True → False) ∨ ((True ∧ True) → ((p3 ∧ (((p2 ∨ (False → False)) → (True ∧ p3)) ∧ p4)) ∨ (((p1 ∧ (p5 ∧ p3)) ∨ True) ∨ (p1 ∧ p5))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49196990967426370190777808648 : (((((True → p3) ∧ p4) ∨ ((p1 → (p3 ∧ p3)) → ((p1 ∨ (p4 → (((p5 ∨ True) → False) ∨ p5))) ∨ True))) ∨ ((p1 → p4) ∨ p2)) ∨ p4) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151381107823701133932746945462 : (((((((p2 ∨ (((p3 ∧ p5) ∨ p2) ∧ p1)) ∨ p1) ∧ (p2 ∧ p3)) ∨ p2) ∧ (p2 → p3)) ∧ (False → p3)) → (((p2 ∨ p3) → p4) ∨ p2)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h8.left
        let h12 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- Conjunctions on the left can always be decomposed.
          let h19 := h8.left
          let h20 := h8.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h19
        case inr h21 =>
          -- Conjunctions on the left can always be decomposed.
          let h22 := h8.left
          let h23 := h8.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h22
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h8.left
      let h26 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h25
  case inr h27 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40380571051116213701543371608 : (((((p2 ∨ ((((((p1 ∧ True) → True) ∨ p2) ∧ p1) ∨ ((p2 → p3) ∨ (p4 ∨ p4))) ∨ (p5 ∧ False))) ∧ (False ∧ p1)) ∨ True) ∨ p1) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232696912349483336391736678553 : ((p1 ∧ (p1 ∨ True)) → (((((p1 ∨ False) → (((((((p4 ∧ True) ∧ (p2 → False)) ∨ p4) → False) ∧ p4) → p1) → False)) → p2) → p5) ∨ p1)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323263677093982089262216463688 : (p5 ∨ ((False ∨ (p5 ∨ (((((p5 ∨ p5) ∨ p1) ∧ p4) ∧ (p3 → (p5 → (p2 ∧ (((p3 ∨ p2) → True) ∧ p5))))) ∨ p2))) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147926332216360944925516528967 : ((((p1 ∨ (((True ∧ p2) → (True ∧ p5)) ∨ False)) ∧ (((True → p2) → (p4 ∨ p3)) ∧ p4)) ∧ (p4 ∨ False)) ∨ ((p5 → p1) → (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_820156254007523856252651701635 : ((((((p2 → ((False ∧ (((p1 ∨ p1) → p1) ∧ (p2 ∧ (False → p5)))) ∧ (False ∨ p1))) ∧ p2) ∧ (p3 → (p5 → (True ∧ p2)))) ∧ p4) → p3) ∧ True) := by
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64107719062609634560618367786 : ((False ∨ ((True ∧ (((p5 → p2) ∨ (False ∨ False)) ∨ p3)) ∨ ((True ∨ (p3 ∨ ((p4 → p1) ∧ p3))) → ((p2 ∨ p5) ∧ (p3 ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115987779069940850017654545130 : ((((p5 → (p4 ∧ p4)) ∨ p3) → ((p5 ∧ (((p3 ∨ p2) → (p5 ∨ p3)) → (p5 ∧ (p2 ∨ ((False ∧ p3) ∧ p5))))) → p3)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45858896112710187406209720263 : (((p3 → (((((((p3 ∨ (True → p1)) ∧ False) → (False ∨ p1)) → ((p3 → p1) ∨ (p3 ∨ p2))) → (p3 → p3)) ∧ p5) ∨ p1)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255180024467315189152559077180 : ((p4 ∧ p4) → ((((p3 ∨ (p4 ∧ p3)) ∨ (((((((p1 → p5) → False) ∧ p1) ∨ (p2 ∧ p2)) ∧ (p2 → p1)) ∧ p1) ∧ p5)) ∨ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193877189260674409797691849115 : ((False ∨ (((p5 ∧ (p5 ∧ p5)) → (p3 → True)) → True)) → ((p4 → (p3 → p3)) → ((p5 → (p1 ∨ ((p5 ∨ p2) → (p2 ∧ False)))) ∨ True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157043215068589457565394011412 : (((False ∧ ((True ∧ ((p5 ∧ (((p3 → (p1 ∧ p5)) ∨ p5) ∨ p2)) ∨ (True → False))) ∨ p2)) ∨ True) ∨ ((p3 ∧ False) → ((p2 ∨ p5) → p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149565476060753964341524794295 : ((p2 ∧ (True ∧ (p4 ∧ (p5 → (p3 → (((p1 ∧ p4) ∨ p2) ∧ ((p2 → True) ∨ ((True ∨ False) ∧ p2)))))))) ∨ (p3 ∨ ((p5 → p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178120649451016534874224018014 : ((((True ∨ (p1 ∨ (p3 ∧ (p5 ∧ p4)))) ∧ (True → (p2 → p5))) → p4) ∨ ((((p1 ∧ (p5 → p2)) ∨ (p3 ∧ p5)) → (p2 ∨ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135710782712134138627071948596 : (((p2 ∧ ((((p2 ∧ (False ∧ p1)) ∨ p2) ∨ ((p3 → p5) ∧ p1)) ∧ p5)) ∧ (p5 ∨ ((False → (p5 → p5)) → True))) ∨ (True ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117303790924540882689508997174 : ((False ∧ ((p5 → ((True ∨ (True ∧ p4)) ∧ (True → (((p1 ∨ p5) ∧ (p5 → (p3 ∨ (p4 ∧ p5)))) → p5)))) → (p3 ∧ True))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177684860282917733836630987246 : ((((p4 ∨ ((False ∨ ((p5 ∧ p4) → False)) ∨ (True ∨ True))) → False) ∧ p2) ∨ ((p1 ∨ (((p2 → True) ∧ p1) ∨ True)) → (p1 ∨ (True ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112243884619460912371770531563 : (((p3 ∨ (((p3 ∧ (p4 ∧ ((p2 ∨ p3) → True))) → ((True → True) ∧ False)) ∨ ((p2 ∨ True) ∨ ((False → p2) ∨ p5)))) ∨ p3) ∨ (False ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82343995170955845480350219749 : ((((((True ∨ (p4 ∧ p2)) ∧ ((False → (True ∨ False)) → False)) ∨ p5) ∨ (p5 ∨ (False ∧ (p4 ∨ p5)))) ∧ (p3 → ((p3 → p4) → False))) → p5) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h9 : (False → (True ∨ False)) := by
          -- Implications on the right can always be decomposed.
          intro h10
          -- False on the left can always be used.
          apply False.elim h10
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h11 := h7 h9
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h15 : (False → (True ∨ False)) := by
          -- Implications on the right can always be decomposed.
          intro h16
          -- False on the left can always be used.
          apply False.elim h16
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h17 := h7 h15
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- False on the left can always be used.
      apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48849329279573240575134603535 : (((p2 ∨ ((((((p3 ∨ p3) ∧ p3) ∧ p4) ∨ ((p4 ∨ (p2 ∨ (p3 → p1))) ∧ True)) ∨ p5) ∨ (p3 → False))) ∧ ((p5 ∨ False) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330964054435223064507598926551 : (True → (p5 → ((((p1 → False) ∨ ((((False → p5) ∨ ((p5 ∧ (True → True)) ∧ True)) ∧ p3) → ((p2 ∧ False) ∧ p5))) ∨ (True → p5)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698956186386308090148379347625 : ((((p5 ∧ (((p5 ∨ ((p2 ∧ (p2 ∧ p1)) → p4)) ∨ True) → p1)) ∨ ((((True ∧ (p4 ∧ ((p2 ∨ p5) → p2))) → p1) → p1) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



