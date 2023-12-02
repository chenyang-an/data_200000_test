variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314506192829808690487804712622 : (p3 ∨ (((p4 → ((p1 ∧ ((p3 ∧ True) ∨ p4)) → (p2 ∨ ((p5 ∨ p5) ∧ p4)))) ∨ (p3 ∨ True)) ∧ ((((True ∧ True) → p2) ∨ p1) → True))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666440776447372037947774639995 : (((((((p2 ∨ p4) ∨ (p3 ∧ p5)) → (((p5 ∨ False) ∧ p5) ∧ ((True → p2) ∨ p3))) → (p1 ∧ (p5 → p2))) ∧ ((p2 → p5) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738831650590656398488308023428 : ((((p2 ∧ p5) ∨ ((p1 ∨ (p2 → (p2 → ((p1 → ((True → p5) ∧ (True → p3))) ∨ p1)))) ∨ ((True → (p3 ∨ (p3 → p2))) ∨ True))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_328830120296240250098601593265 : (True → (((p5 → False) → (True ∧ ((p2 → (p4 ∨ p5)) ∧ True))) → (((((True ∨ p4) ∨ True) ∨ False) → False) ∨ (False → (p2 → (p2 ∧ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201220855618536459053438456019 : ((p2 → (((p3 → p2) → p5) ∨ (p2 → p5))) → ((p1 ∨ p5) ∨ ((False ∧ (((p4 → p2) ∧ (p3 ∨ p4)) → p2)) ∨ ((p1 ∧ p2) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66657049575111922973983531847 : ((True → (((((p3 ∧ p5) → (True ∨ p3)) → p5) → False) ∨ (False ∧ ((p3 ∧ p2) ∧ (((p2 → ((p3 → p1) ∨ True)) ∨ p3) ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611475752410759486450226340895 : (((((p3 ∧ (((((p3 → (p3 ∧ (p3 ∨ p3))) ∨ p3) → p4) → (True ∧ p1)) ∧ ((p4 ∧ p1) → (p1 ∧ (p3 ∧ p1))))) → p4) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344135672872361798115506971421 : (p2 → (False ∨ (((p4 → False) → p5) → ((p4 ∨ (p4 ∨ (p4 ∨ ((True → True) ∨ p5)))) → (p4 → (((p4 → p2) ∧ (p3 ∧ p5)) ∨ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655436155092601570601636010316 : ((((((p3 ∧ False) ∨ ((((((p2 ∧ (p5 ∧ p4)) ∨ ((p3 ∧ p2) ∧ p5)) ∧ p5) → False) → p4) ∧ p3)) ∨ (False ∧ p4)) ∨ (p4 ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67456050402538450226943036242 : ((p1 → (((((p5 ∧ (((((p2 ∨ p2) ∨ p1) → (p3 → False)) ∨ p4) → p5)) ∨ p2) ∨ p1) ∧ False) ∨ (((True ∧ False) ∧ p4) → p2))) ∨ False) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157012192714344808430545024253 : ((((p5 → (p3 ∧ p4)) ∨ (((((((p3 ∧ p2) → p1) ∧ True) ∧ p2) ∧ True) ∨ p2) ∧ p5)) ∨ False) ∨ ((((True → p1) ∨ False) ∧ p2) → p1)) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111063558220222351374773961623 : ((((p3 ∨ ((p3 ∨ False) ∧ (((p5 ∧ ((p5 ∨ p5) ∧ True)) → p1) → p2))) ∧ ((p2 ∨ p3) ∨ ((False → p4) ∨ p3))) ∧ p2) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_459764543741501743593965171874 : ((((((p1 ∧ False) → (p3 ∨ (p3 → (False → p2)))) → (True ∧ ((False ∨ (p2 ∧ True)) → p4))) → ((((False ∧ False) ∧ False) ∨ p4) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51219657592158096956231940770 : (((((p3 ∨ (p2 ∧ False)) ∨ (p1 → False)) ∨ (((p4 → p2) → ((False ∨ True) ∨ p1)) ∧ p2)) ∨ (((p4 ∧ p1) ∧ (True ∧ False)) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198657028912371849473610730578 : ((p3 ∨ (p3 ∨ (((p2 → p1) → p4) ∨ p5))) ∨ ((True ∨ p4) → ((p4 ∧ ((p2 → p2) ∧ (((True → (True ∨ p1)) ∧ p1) → p2))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84673897968462659725246391043 : ((((((((p3 → p4) → (True ∨ (True ∨ p4))) → p1) ∧ p1) ∨ False) ∨ p1) ∧ (p5 → (((True ∨ False) ∧ (True ∧ (p2 ∧ p2))) → True))) → p1) := by
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
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735529769997179558609223549947 : ((((p4 ∨ p5) ∧ (((True ∨ p3) ∨ (p1 ∧ p5)) ∧ ((p4 ∧ (p1 → ((False ∨ p5) → False))) → ((p4 ∨ ((p1 → p2) → p5)) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314401254575904916049365091115 : (p3 ∨ ((((((p5 ∧ p1) ∧ ((p4 ∧ (p2 ∧ (True ∨ (True → p1)))) ∨ p3)) ∧ False) ∨ (p5 ∨ p3)) ∧ p2) ∨ ((p5 ∧ p1) → (True ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_650662685592275824902072255813 : (((((((((p5 → p1) ∧ p1) → p3) → p5) ∨ (False ∧ p2)) ∨ (((p5 ∧ (True → (p1 → p4))) → p2) → (p3 ∨ p1))) ∧ (p1 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200764659362950096557938092934 : ((p4 ∧ ((True → ((p1 ∧ p1) ∧ False)) ∨ p3)) → ((((p3 → (False ∧ p4)) ∧ p4) ∧ p1) → ((p2 → p2) ∧ ((p4 ∨ (True ∧ p3)) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Implications on the right can always be decomposed.
  intro h12
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h2.left
    let h15 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h1.left
    let h19 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h21 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h22 := h20 h21
      -- We need to get the right conjuct of h22 based on <expert-advice>.
      let h23 := h22.right
      -- False on the left can always be used.
      apply False.elim h23
    case inr h24 =>
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h25 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h24
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h26 := h16 h25
      -- We need to get the left conjuct of h26 based on <expert-advice>.
      let h27 := h26.left
      -- False on the left can always be used.
      apply False.elim h27
  case inr h28 =>
    -- Conjunctions on the left can always be decomposed.
    let h29 := h28.left
    let h30 := h28.right
    -- Conjunctions on the left can always be decomposed.
    let h31 := h2.left
    let h32 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h33 := h31.left
    let h34 := h31.right
    -- Conjunctions on the left can always be decomposed.
    let h35 := h1.left
    let h36 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h36
    case inl h37 =>
      -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
      have h38 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h37, we can now drive its conclusion.
      let h39 := h37 h38
      -- We need to get the right conjuct of h39 based on <expert-advice>.
      let h40 := h39.right
      -- False on the left can always be used.
      apply False.elim h40
    case inr h41 =>
      -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
      have h42 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h41
      -- We have shown the premise of h33, we can now drive its conclusion.
      let h43 := h33 h42
      -- We need to get the left conjuct of h43 based on <expert-advice>.
      let h44 := h43.left
      -- False on the left can always be used.
      apply False.elim h44



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229602761667156036496008289779 : ((p3 → (p3 ∧ p4)) ∨ ((p2 ∧ (((((False ∨ p1) → True) ∧ (p1 → p5)) ∨ False) → (((p3 → p5) ∨ p4) → (False ∨ p4)))) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84089666438757116637559325129 : ((((True ∨ (p4 ∧ (p4 → p2))) ∧ (((p4 ∨ False) → (p4 → False)) ∨ (False ∨ p3))) ∧ (p2 ∧ ((False ∨ False) → ((p5 ∧ True) ∧ p3)))) → p2) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h3.left
      let h9 := h3.right
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h3.left
        let h14 := h3.right
        -- One of the premise coincides with the conclusion.
        exact h13
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h3.left
      let h20 := h3.right
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h3.left
        let h25 := h3.right
        -- One of the premise coincides with the conclusion.
        exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806239989645025450941999286413 : (((p4 → ((((False ∨ p3) ∨ (((True ∧ False) → True) → ((p3 → ((p2 ∧ p3) ∨ p2)) ∨ (p5 → p4)))) ∧ (False → (p2 → p1))) ∨ False)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616225680391256502830399635800 : (((((p1 → (((p3 ∨ p2) ∧ ((p2 ∧ False) → (p3 ∧ p3))) ∧ p5)) ∧ (((True → p2) ∨ ((False ∧ (True ∧ p2)) → p3)) ∧ p4)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310412873556156274382000990084 : (p2 ∨ ((((((False ∧ p3) ∨ True) ∧ p3) ∨ p3) ∧ p5) → ((((p2 ∧ (p4 ∧ True)) ∨ p3) ∨ (((p1 → (p5 ∨ False)) ∨ p3) ∧ True)) ∨ False))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_812973589980359137474860404199 : (((((((p2 ∧ p2) → False) ∧ (((p4 ∨ (p5 → ((False ∨ p1) → ((False → p3) ∨ p4)))) → p5) ∨ ((False ∨ p5) → p1))) ∧ True) ∧ p2) → False) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : (p2 ∧ p2) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h12 : (p2 ∧ p2) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h13 := h6 h12
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198210451511161880060361113598 : (((p5 → True) → ((p1 → (p3 ∧ p3)) ∨ p4)) ∨ (((p2 → (True → (((p1 ∨ ((p5 ∨ p1) ∧ p1)) ∨ p2) → (False ∨ p4)))) ∧ p1) → p1)) := by
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
theorem thm_5_vars_328122148359700203096244453652 : (True → ((((p4 ∨ ((False ∨ p4) ∨ p4)) ∧ (p4 ∧ (p2 ∧ False))) ∨ (p1 ∨ ((p2 ∨ (False → (p4 ∧ True))) → True))) ∨ ((p1 ∧ True) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_324092998271395467363756945110 : (p5 ∨ ((p2 ∨ (p3 ∧ ((((p3 ∧ p4) ∧ (p1 → False)) → p3) → p1))) ∨ (p1 → (p4 → (p1 ∨ (p2 → ((p4 ∨ p2) → (p4 ∨ False)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48998895352002589404085239904 : ((((p5 ∨ (p1 → (((False ∨ ((p1 ∧ True) ∧ ((False → (p4 → p2)) → p4))) ∨ (p2 → p5)) ∨ p3))) ∨ p3) ∨ (True ∧ (p4 ∨ True))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248143312939111192655692499575 : ((p2 ∨ False) ∨ (((p3 ∨ (p3 → ((True → p3) ∨ p4))) → ((p1 ∨ (p1 ∨ (p1 ∨ (True → (p2 ∧ ((p1 → p4) ∧ p1)))))) ∧ p4)) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ (p3 → ((True → p3) ∨ p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
        have h13 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h12, we can now drive its conclusion.
        let h14 := h12 h13
        -- We need to get the right conjuct of h14 based on <expert-advice>.
        let h15 := h14.right
        -- We need to get the right conjuct of h15 based on <expert-advice>.
        let h16 := h15.right
        -- One of the premise coincides with the conclusion.
        exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150537877691613211993214132593 : ((((((p1 → (False → p4)) ∧ (p3 ∨ False)) ∧ p4) → (False → (p2 ∧ ((p5 → False) → (p2 ∨ False))))) ∧ p5) → (p5 → (p2 → (p2 ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66373745106099252892583928828 : ((p5 ∨ (p2 ∨ (True ∧ ((p3 ∨ p4) → ((((p4 ∧ (False ∨ p5)) ∧ ((p1 ∧ p5) ∧ p2)) ∧ p1) ∧ (p4 ∨ ((p1 → p3) → True))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238333187660889911781145772323 : ((False ∨ True) ∧ ((p1 ∧ p3) → (False ∨ (((p1 ∧ (((((p4 ∧ (p5 → p3)) ∧ (True ∨ (p4 → p5))) ∧ True) → False) → p1)) → p5) ∨ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_173472677500452308878112840529 : ((((False ∨ (((p3 ∨ True) ∧ (p3 → (True ∧ p3))) ∨ (p1 ∨ True))) ∨ p1) ∧ p2) → (True → ((p4 ∨ p1) ∨ ((p1 ∧ (p4 → False)) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
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
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h18
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h19 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_27206823541054728564670076428 : (((p3 → p4) ∨ (p1 ∨ (((p1 ∧ (((p3 ∨ ((p4 ∧ p1) ∨ False)) → p2) ∧ p3)) ∨ (((p1 → p5) → p2) ∨ (False → False))) ∨ p4))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229963016891729039872536487422 : (((True ∧ p4) ∧ p4) → (p4 ∧ ((p4 ∨ ((p4 → (False ∧ p4)) → p4)) → ((True ∨ False) → (((p4 ∨ (p2 ∨ True)) → (False ∧ p3)) ∨ True))))) := by
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
  exact h3
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h1.left
      let h11 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h1.left
      let h16 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h19 =>
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135833708638874942322442610886 : (((((p1 ∧ p3) → False) ∨ (p5 ∧ (p5 ∧ (p3 → (True ∨ p3))))) ∧ (((p4 → (p3 → p4)) ∨ False) ∧ (False ∧ False))) ∨ (p4 → (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137388544512982344953201729116 : ((p3 ∧ ((p4 ∨ p2) ∧ (p2 ∧ (p1 ∨ ((p1 ∨ (p4 ∨ ((False ∨ p4) ∨ p2))) ∧ (((True ∧ p2) ∨ p1) → p4)))))) ∨ ((False ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231334820315013174205720580256 : (((True → p3) ∨ p4) → ((((p4 ∧ p2) → ((False ∨ p2) ∨ (True ∨ p5))) → False) ∨ ((p1 ∧ p1) ∨ (((False ∧ p5) ∧ True) → (False ∨ p5))))) := by
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
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358694350514073879240127652912 : (p5 → (p4 → (p5 → ((p4 ∧ (((p1 ∨ (p2 ∨ p4)) → (p2 ∧ (((False → p5) ∧ p1) ∨ (p5 → False)))) ∨ (False → True))) ∨ (p5 ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809779830295225612834313622887 : (((p5 → (((((False ∧ p4) → p4) → (p3 → ((p4 ∨ p1) → p2))) ∨ ((((p1 ∨ p2) ∧ (p2 ∨ p4)) → p1) ∧ p2)) ∨ (True ∧ p5))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587864060899944904402559022539 : (((((((p3 ∧ (p1 ∧ (((((p1 → ((p4 ∨ p3) ∧ True)) ∨ p5) ∧ p4) → (p3 ∨ p2)) ∧ p5))) ∨ True) → (p5 ∧ False)) ∨ p5) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650149844511010360808941746194 : ((((((False ∨ (False ∧ (False ∧ p3))) ∨ (False → ((((p4 ∧ True) ∧ True) ∨ p1) ∨ True))) ∧ (p1 → ((p3 → p1) ∧ p2))) ∧ (p3 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171747460866297660671865938446 : (((((False ∨ True) → ((((p5 ∨ p1) ∨ p4) → p4) ∨ (p4 ∧ p5))) ∨ True) → p5) ∨ (True ∨ (True ∧ (((False ∧ (p1 → False)) ∧ True) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304108635267877211028346346176 : (p1 ∨ ((p2 → ((True → ((p3 → False) ∧ (p3 ∧ (False ∧ ((True → p5) ∧ (((p3 ∨ p4) → p5) ∨ (p4 ∧ p3))))))) ∨ (True ∨ p4))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639294760287047582145836213260 : (((((((p2 ∧ p5) ∧ p5) → True) → (((((p4 ∧ (p3 → p3)) ∨ p4) ∨ ((p2 ∨ True) → ((p5 ∧ p5) → False))) ∨ p4) ∧ p1)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170322032581675838574961693571 : (((True → ((p5 ∧ False) ∨ False)) ∨ (p4 ∨ ((((p3 → p4) ∨ False) ∨ True) ∨ p1))) ∧ (((((p1 ∨ p4) ∨ p4) ∨ False) → (p1 ∨ p4)) ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h5 =>
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
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167114927926478718906710354462 : (((((False → (p4 → (p2 ∧ (p3 → p5)))) ∧ (p4 ∧ p5)) ∨ (False → (p2 ∨ False))) ∨ True) → (p1 ∨ (False ∨ (p4 ∨ (True ∨ (p2 ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
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
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
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
  case inr h9 =>
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
theorem thm_5_vars_791598769718069249672944058389 : (((True → (((((p3 ∨ (p3 ∨ p5)) → (p3 ∨ (p5 ∧ (False ∧ p5)))) ∧ ((p3 → (True → ((p4 ∨ p2) ∨ False))) → p3)) → p4) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345472604896263718889273413775 : (p3 → (((((p1 ∨ p5) ∧ True) ∧ ((True → p4) → (p1 ∧ (p5 ∨ ((p2 ∧ p5) ∨ ((p3 ∨ True) → False)))))) ∨ (p3 → (p5 → p3))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172996432926310503096029765917 : ((p5 ∧ (((((p5 ∨ p1) ∨ p3) → (p5 ∨ False)) → p4) ∧ ((True ∧ p1) → p2))) ∨ (((p1 ∧ ((p1 → (p2 ∨ p5)) → p2)) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66334059597556636515223978496 : ((p5 ∨ (p2 ∧ ((p2 ∧ p3) ∨ ((False ∧ p3) ∧ ((((p5 ∧ True) ∨ True) ∨ (False ∨ ((True → ((True ∧ p5) ∨ p4)) ∧ True))) → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56638571919352435783057480963 : ((((True ∨ p1) ∧ p2) ∧ (p4 → ((((False ∨ ((p1 ∧ (p3 ∧ (p5 ∨ p5))) ∨ (p2 ∨ (False → p1)))) ∧ (False ∨ p1)) → p3) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301410364267709919530592453542 : (False ∨ (((p4 → (False ∨ p4)) ∧ p1) → (((False ∨ (False ∧ p3)) ∧ ((p5 ∨ ((p4 → p3) ∨ p4)) ∨ p3)) ∨ (p3 ∨ ((p2 ∨ False) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708628387682796910763832798869 : (((((False → ((True → True) → (p1 ∧ p3))) ∨ False) → (((False → p3) → (p4 ∧ p5)) → (((p5 ∧ (p2 ∨ (p3 → p3))) ∨ True) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149368592092217997764712157304 : (((False → p5) → (((p3 ∧ False) ∧ ((p5 → (((False → True) → (True → (p2 → False))) ∨ p2)) ∧ p3)) ∧ p3)) ∨ (p1 ∨ (False → (p2 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658586129320152945585539273156 : ((((p3 ∨ (((((p5 ∨ p5) ∨ False) ∨ ((((p4 ∨ (p3 ∨ p1)) ∧ p4) ∧ (True → p1)) ∨ True)) ∧ (p3 ∧ p1)) ∨ p2)) ∨ (p1 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678363082481534188765489097705 : (((((True ∧ ((p5 ∧ p4) ∨ (p3 ∨ p2))) ∨ (((p4 ∨ (p3 → p3)) ∨ (p1 ∨ p5)) ∧ (p4 ∨ p3))) ∨ (p1 → ((p5 → p5) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47369179782811323424096308774 : ((((p2 → False) ∨ (((p5 → (((False ∨ p3) ∧ True) → p4)) → ((False ∨ True) ∨ ((p4 → p5) ∨ False))) → (p5 ∧ p2))) ∨ (True ∨ p5)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52279500020752245385956755482 : (((p2 → (True → ((p2 → (((p4 → p3) → False) ∧ p5)) → ((True → False) → p1)))) → (((((p1 ∨ p1) → p3) ∨ p1) ∨ p5) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139641741765372154561992472039 : (((((p1 → p5) ∨ (p3 ∧ (p3 ∨ p1))) ∧ (p3 ∨ ((((p1 ∧ ((False ∨ p5) → p4)) ∨ p3) ∧ p5) ∨ p3))) → False) → (p1 → (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322274653969291750946093333025 : (p5 ∨ (((p5 → ((((((p2 ∧ p1) ∧ (p4 → ((True ∨ (p4 ∨ p5)) → (p5 ∧ (False → p4))))) ∧ False) → p3) ∨ False) → p2)) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314443806969778561333592534262 : (p3 ∨ ((p1 → ((p3 → p5) ∨ ((p3 → (p1 ∨ p2)) → (((p2 → ((False ∧ p1) ∧ True)) → p1) → p4)))) ∨ ((False → (False ∧ p3)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780269903044410116294145517272 : (((p2 ∨ (((((((p3 ∧ ((p1 ∨ p3) → p3)) ∧ (p3 → p3)) ∧ p2) ∧ (p4 ∨ False)) ∧ True) ∧ False) ∧ ((p4 ∨ (p3 → p5)) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55797471506274842542982892704 : ((((p5 ∨ p5) ∨ (p5 ∨ True)) ∧ ((((p5 ∧ (p2 → p3)) ∨ ((p1 ∧ p3) → (((p5 ∧ p4) ∨ (p2 ∧ p2)) ∨ p3))) ∨ p1) ∧ True)) ∨ False) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115044877289842895660310764326 : ((((p4 ∧ ((p1 → False) ∧ ((True ∧ p1) ∨ (p2 → False)))) ∨ False) ∨ (p5 ∨ ((p5 ∨ (p4 ∨ True)) ∨ (p1 ∨ (p1 ∨ p4))))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149175860447555978103551079590 : (((True → p2) ∧ (p2 ∨ (p5 ∧ (p3 ∨ (p1 ∨ ((p3 → p1) ∧ ((p4 ∧ ((True ∧ p3) ∨ p5)) ∧ p3))))))) ∨ ((p1 → p3) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218545938441202738028481481075 : (((True → True) → (p1 ∨ p2)) → ((((p1 → p1) → ((((False ∨ (p3 ∨ (p4 ∨ p2))) ∨ (p1 ∨ p1)) ∨ p3) → (False ∧ p3))) ∧ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_478304331930536901836156513851 : ((((False ∨ ((p2 → p1) ∧ (True → ((p5 ∧ p1) ∨ False)))) → (((p5 → p4) → (p5 ∧ (p2 ∧ p3))) ∨ ((True ∨ (p1 ∨ p4)) ∨ False))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649856051308386449592652341580 : (((((((p2 ∧ (False → (True ∨ (p2 ∨ (((p1 ∨ (p3 ∧ p3)) ∧ True) → p3))))) → p5) ∧ False) ∧ ((False → p2) → True)) ∧ (p5 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53356902428457155673215951237 : ((((((True ∨ ((True → True) ∨ p4)) → p3) ∧ (p1 → p1)) ∨ p4) → ((True → (((p1 ∧ False) → (p1 ∨ p4)) → (p4 ∧ p5))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798465614152174580401371318604 : (((p1 → ((((((p1 ∨ (p2 ∧ p3)) ∨ p2) ∧ p4) ∨ False) ∧ p4) → (((False → (p5 ∨ True)) → (p5 → p5)) → ((p4 → p5) ∨ p4)))) ∨ p2) ∧ True) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345558905617875679947846629791 : (p3 → ((((p3 ∧ (p1 ∧ p1)) ∨ False) ∨ ((p2 ∧ (((p3 → (False ∧ (True ∧ False))) → p2) ∨ p5)) ∨ ((p5 ∧ p1) → (True → p3)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46561340093664228838981280753 : ((((True → False) → (False ∨ ((p5 ∨ ((p2 → p3) → (p3 ∨ p2))) → (p4 ∨ (False ∧ ((p2 ∨ p4) ∨ (False → p2))))))) ∧ (p1 → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228568740899374393573574750644 : ((p1 ∨ (p1 ∨ p5)) ∨ (((((((p2 → p1) → p4) → ((p1 ∧ (p3 → p5)) → p3)) → p5) ∧ (((p5 → p4) ∨ False) ∨ False)) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346904582623453793013823686693 : (p3 → ((((True ∨ True) → (((p3 ∧ ((False ∨ p3) ∨ p5)) ∨ p3) → (p3 ∧ False))) ∨ (p4 → True)) ∨ ((p4 → (p4 → (p5 ∧ p1))) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172128639893763601999546938345 : ((((p3 ∨ ((p2 ∧ p3) → False)) ∧ ((True ∧ False) ∨ p2)) ∧ (p2 ∧ (p1 → p4))) ∨ (True ∨ (p4 ∨ ((p1 ∧ (p2 ∧ False)) ∧ (p5 → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65338982250013610064938311888 : ((p3 ∨ ((True → (False ∨ (((True ∨ ((p5 ∧ True) ∨ True)) ∨ p4) ∧ (((True ∨ p1) → p4) → True)))) → (False ∧ (p1 → (True ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112698742863674384537880888734 : ((((True ∧ ((p2 ∧ p2) → ((True ∨ ((p2 → p1) → (p4 ∧ (p2 ∨ p3)))) → True))) ∨ (((False ∨ p2) ∧ p5) ∨ p5)) → False) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171963878314443402297425543403 : ((((p5 → p2) ∨ ((False ∧ (False ∨ (p4 ∨ (p4 ∨ p2)))) ∨ p4)) ∧ (False ∧ False)) ∨ ((p2 ∧ ((((p5 ∨ p5) ∧ p5) ∨ p1) ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42390044009271286050671818352 : (((p4 ∧ (((p3 ∨ p2) → (False ∧ p2)) ∧ ((((((False ∨ p1) ∨ p2) ∧ p3) ∨ (((p3 ∧ p4) ∨ p1) ∨ p1)) ∧ True) → p4))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64651493693777919394396113862 : ((p1 ∨ (p5 ∧ (p1 ∨ ((p5 ∧ p1) ∨ ((p3 → ((p2 ∧ ((p4 → (p2 ∨ p3)) ∧ p3)) ∧ (p3 ∨ (True ∧ (p5 ∧ p4))))) ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705206814104079077787785921006 : ((((((p5 → p1) ∧ ((p4 → p5) → p5)) ∧ p3) ∧ (((p4 ∧ (p5 → ((p5 → p3) ∨ True))) ∧ (p5 ∧ ((p5 ∧ True) ∧ True))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66490541074925139649412743255 : ((True → (((((True ∨ p1) ∧ p5) ∧ (((p1 ∨ True) → False) ∨ False)) ∨ ((p5 ∧ (p1 → (p2 → ((True ∨ True) → p2)))) → p1)) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192255446086331691110977891339 : ((((p5 ∧ (p4 ∨ True)) ∧ (p5 ∧ (p1 → p3))) ∧ True) → ((p2 ∧ (p2 ∨ (False → p5))) ∨ (((True ∧ p2) ∧ p2) ∨ ((False ∧ p1) → True)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h5.left
    let h10 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h5.left
    let h14 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38275815021379133448946296188 : (((((p4 → ((p2 ∧ (False → False)) ∧ ((p4 ∨ p3) ∧ (p1 ∧ (p4 → False))))) ∧ (False ∨ True)) ∨ (p1 ∧ (p1 → (False ∨ p2)))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_878164931045609862139473670878 : (((((p5 → p5) ∧ (((False → (p4 ∧ p2)) ∨ ((((True → p1) ∨ p3) → p3) → (p2 ∨ ((p3 → False) ∨ p2)))) ∧ p4)) ∧ (p1 → p1)) → p4) ∧ True) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707920102370385188467648198874 : ((((p5 ∧ (((p5 ∨ p2) ∨ (False ∧ p3)) → p2)) ∨ (((p3 → p5) ∧ (p1 ∨ (p5 → True))) → ((True → (p3 ∧ (p3 ∨ False))) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148601087140721557608767831220 : (((p2 ∨ (p4 ∧ (False ∧ (((p1 ∧ p4) ∨ p4) → p2)))) ∨ ((p1 ∧ (p1 ∧ (p1 → (True → False)))) → p2)) ∨ (p2 ∨ ((p2 ∧ p2) ∧ p1))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757556760063964484581909045234 : (((p1 ∧ (p2 ∧ ((p4 ∧ (p4 ∧ ((((True ∨ True) ∧ (p2 ∨ (False ∨ ((p5 ∨ p5) ∨ p2)))) ∨ p2) ∧ p4))) ∧ ((False ∧ p4) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245238985014633383894247687633 : ((p2 ∧ p1) ∨ (((((((p4 ∨ (p1 ∧ p3)) → p2) ∧ (p2 ∧ p1)) ∧ (True ∧ p5)) ∧ p2) ∨ (True → p2)) ∨ ((p2 ∨ p2) ∨ (p2 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175236419326070301710620058850 : ((p1 ∨ ((p2 ∨ p5) ∨ ((p3 → ((p3 ∧ (p4 ∨ p1)) → p5)) ∧ (True → p1)))) → (p4 → (p3 ∨ (((p3 ∨ True) ∨ True) ∨ (True ∧ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709232103227910278117077115132 : (((((p1 ∧ False) ∨ (False ∨ (False → (p3 → p1)))) → ((p1 ∨ (((p4 ∧ p3) ∨ p2) → (p2 ∨ (p4 → p2)))) ∧ ((p1 → p2) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678606863685985681343671056086 : (((((p4 ∧ p2) ∧ (((True ∨ p3) → (True ∨ ((p5 ∧ p5) ∨ False))) ∨ (p3 ∧ (False ∧ (p4 ∧ True))))) ∨ ((p4 ∧ (p1 → p4)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181596257060603252659317540027 : ((p1 → (p4 ∧ ((((p2 ∧ True) → p4) → (p2 → (p5 ∧ p1))) ∧ p3))) → (((p2 → (((p2 → p5) → False) ∧ p5)) ∨ True) ∨ (False ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199397355630299595952227924676 : ((((False ∨ p4) ∧ (p3 → (p5 → True))) ∨ False) → ((p4 → ((p4 → True) → (p5 ∧ (p2 ∧ (p4 ∨ ((p3 → p4) → p1)))))) ∨ (False → p5))) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674855873810208390791792439005 : ((((((((False ∧ ((False → (p5 ∧ (p1 ∧ (False → False)))) ∨ p5)) ∨ (False ∧ p4)) ∧ True) ∧ p2) ∧ p5) ∧ ((p3 ∨ (True ∧ False)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208511124515923012311211761084 : (((p3 ∧ p1) → (True ∧ (p4 ∨ p1))) → ((p5 ∨ (((p5 ∨ (p5 ∨ False)) → p2) ∨ ((p2 → (p5 → p2)) ∧ ((p1 → False) ∨ True)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42529339445286843286172610290 : (((p1 ∨ ((((p4 ∧ p4) ∨ (((p1 → p5) ∨ (False → p2)) → ((p1 ∧ (p3 ∧ p1)) ∨ ((p5 ∧ p3) → p5)))) ∨ p1) ∨ p1)) ∨ p5) ∨ p1) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8



