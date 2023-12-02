variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65474381895308933164842013433 : ((p3 ∨ (False ∧ (p5 → ((p3 → ((p1 ∨ (((p3 ∧ False) ∨ (False → (True → (False → p3)))) ∨ (p1 → (p1 → False)))) ∧ p2)) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152282873590219859922021542364 : ((((p5 → (p4 ∧ False)) ∨ (p3 ∧ p1)) → (((p3 → (p1 → p2)) ∨ p3) ∨ (p2 ∧ ((p3 → p2) ∨ True)))) → (True ∧ (p2 ∨ (p2 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171301307301860618384814307826 : ((((((p3 ∨ ((p1 → True) → False)) ∧ False) ∨ (p1 ∨ (p5 → False))) ∧ p4) ∧ False) ∨ ((p3 → ((p1 ∧ p4) → ((True ∨ p1) ∨ p1))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_42361731446551242264422482907 : (((p3 ∧ (p1 ∨ (False ∧ (((False ∨ p3) ∨ True) ∨ ((p4 ∧ (p4 ∧ (p4 ∨ p4))) → ((p4 ∧ ((p5 → p5) ∨ p3)) ∨ p1)))))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200200613091868262228670245285 : (((p5 ∨ (p4 ∧ p2)) ∨ ((p1 ∨ p3) ∧ True)) → (((p3 → ((((p2 ∧ (True → (p3 ∨ p4))) ∨ (p2 ∨ p4)) → p1) ∨ p2)) ∨ True) ∨ p4)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
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
theorem thm_5_vars_256733589721458046955767434759 : ((p1 ∨ p1) → ((True → p2) ∨ ((p2 → (p3 ∨ ((p5 ∨ ((p4 ∧ (p3 ∧ (p4 ∨ p4))) ∨ False)) ∨ (p5 → (False → (p1 ∨ p5)))))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60798924469805225252744488958 : ((True ∧ (p1 ∧ (((p4 ∨ ((((((p4 ∧ ((p3 ∧ (p5 → (p3 ∨ True))) ∧ p2)) ∧ True) ∧ p1) → p3) ∧ p2) ∨ p2)) → False) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301827920206531123500242063035 : (False ∨ ((p2 ∨ p4) ∨ (((p2 ∨ ((((p5 ∨ p3) ∨ p3) ∧ True) → True)) ∧ ((p3 ∨ p1) ∧ ((p2 → ((p3 ∨ p4) → p3)) ∧ False))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156679848458382699704769031356 : ((((True ∧ ((p3 ∧ (p1 → ((p5 ∧ p3) ∧ (p2 ∨ (False ∨ p5))))) ∨ p1)) ∨ (p3 → True)) ∧ p1) ∨ ((p2 ∨ ((False ∧ p5) → p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307362164306573387914043179150 : (p1 ∨ (p4 ∨ (((True → (p5 → (p3 ∧ (p1 → (((False ∨ (p2 → (p4 → False))) → (True ∧ p2)) ∨ (p5 ∨ (p5 ∨ p5))))))) ∨ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85725204814950040509296549529 : (((((p1 ∨ True) → ((((p5 ∨ False) ∧ False) → p4) ∨ False)) ∨ p1) → ((p3 ∨ ((((p3 → p4) → p1) ∧ (False → p1)) ∨ True)) → False)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ True) → ((((p5 ∨ False) ∧ False) → p4) ∨ False)) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h15 =>
        -- False on the left can always be used.
        apply False.elim h15
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h2
  -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
  have h17 : (p3 ∨ ((((p3 → p4) → p1) ∧ (False → p1)) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h16, we can now drive its conclusion.
  let h18 := h16 h17
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778897191445126872162135617799 : (((p1 ∨ (p1 → ((p2 → ((False ∧ p5) ∨ (((p1 → ((p5 → ((True ∧ True) ∨ p4)) ∨ p4)) ∧ (p5 ∧ False)) ∨ False))) ∨ (p5 ∨ True)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46795360959264588997678217061 : (((p5 → ((p1 ∧ (True → p5)) ∧ ((p3 ∧ (p5 → (p2 ∧ (((True ∧ p1) ∨ p2) ∨ (p3 ∨ p2))))) → (p4 ∨ p1)))) ∧ (False ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157483053877028043960418599396 : (((((p2 ∨ ((p3 ∧ True) → p2)) ∧ ((p5 ∧ True) ∨ False)) ∨ (p2 ∨ (p3 ∨ False))) ∨ (p1 ∧ p2)) ∨ ((p4 ∨ p4) ∨ ((p5 → p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_504390969603830710305369914708 : ((((True ∨ (p1 ∨ p3)) → ((p1 → False) → (((p2 ∨ (((p3 → True) → p1) → p1)) ∧ (p5 → (p4 → False))) ∨ ((p1 ∧ p4) → p2)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h17 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h18 := h2 h17
      -- False on the left can always be used.
      apply False.elim h18
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300382745799253675228452989823 : (False ∨ (((((p2 → p3) ∧ False) → ((p2 → p2) → ((p1 ∧ p4) ∧ False))) → (((p5 → (p2 ∨ p3)) → p1) ∨ False)) ∨ (p5 → (p5 → True)))) := by
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
theorem thm_5_vars_635969776058740824491601231078 : ((((((p4 ∧ ((True ∨ (p3 ∨ (p2 ∨ p3))) ∧ (p1 ∧ (p5 → (p3 ∧ p5))))) → True) ∧ (((p1 → p1) ∧ True) → (p2 → p4))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1785393586550104095255769620 : (((((False ∨ p1) ∨ (p3 ∨ ((p1 ∧ (True → p1)) ∧ False))) ∨ (p1 ∨ True)) ∨ ((True ∧ (p4 → p2)) ∨ False)) ∨ (p5 ∧ (p5 → p2))) := by
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
theorem thm_5_vars_191550966666735604154689517764 : ((p1 ∧ ((p3 ∨ p1) ∨ (((p4 ∨ p1) ∧ False) ∨ p4))) ∨ (((p1 ∨ (p1 ∨ True)) ∨ p3) → ((True → (p5 ∨ True)) ∨ (p2 ∧ (p1 ∨ p2))))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
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
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685840078191471762924872598252 : (((((((True ∧ False) → p5) ∧ (((p4 ∨ p4) ∧ True) ∧ (p5 ∨ ((False ∧ p1) ∨ p5)))) → p1) → (((p5 → p4) → (p5 ∧ True)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117055856817871242474055352756 : (((p5 ∨ True) → ((p1 ∨ ((p3 ∨ p2) ∧ ((((False → p2) ∧ p5) ∨ p2) → p4))) ∧ (((p1 ∨ True) ∧ (False ∨ False)) ∧ False))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149227765118097724227076582679 : (((p4 ∧ False) ∨ ((((p3 ∨ (p4 ∨ True)) ∧ p3) → False) ∨ (True ∨ (p4 → (True ∧ ((p5 ∧ p3) ∧ p4)))))) ∨ ((p5 ∨ (p1 → p4)) → p3)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39427665819431905630427121799 : (((p4 ∧ (True → ((False ∨ (p3 → (False ∨ (((p1 → p2) ∨ (p1 → p2)) ∨ ((((True → False) ∧ p2) ∧ p4) → False))))) ∨ False))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217261370332415117710874168020 : (((p1 ∧ (p2 ∨ p4)) ∨ True) → (p3 → (p3 ∧ (p4 → (p4 ∧ ((p2 ∧ (p5 ∧ ((p1 ∧ (True ∧ ((True ∧ True) ∨ p4))) ∧ True))) ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h21 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_486461710771557961486182014795 : ((((p2 ∧ ((False ∨ (p4 ∧ p2)) ∨ p4)) ∨ ((((p5 ∧ ((True ∧ p1) ∧ True)) ∨ ((p4 → (False ∨ p3)) ∨ p1)) ∨ (True ∨ p2)) → True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196191436518931412119192988444 : ((False ∨ (p5 ∨ (((False ∨ True) → True) ∨ p4))) ∧ ((((True ∨ (p3 → p4)) ∨ p2) → (p1 ∨ (p5 → (p4 ∨ p5)))) ∨ (p2 → (p5 ∧ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694187616788139214363133190792 : (((((p3 ∧ (p3 → ((p4 ∨ p3) ∧ False))) → ((p4 ∧ (p4 ∧ True)) ∨ p4)) ∨ (p2 ∧ ((p4 ∧ p4) → (((False ∧ p3) ∧ False) ∧ p5)))) ∨ p4) ∧ True) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215109745949636795115446930521 : (((p2 → p1) → (True ∧ False)) ∨ ((p2 ∨ ((p5 ∨ (p4 → (False ∨ p4))) ∨ p1)) ∨ ((p2 ∧ (True ∧ (True ∧ (p1 ∧ (p1 ∧ p5))))) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152043413606632081331431474967 : (((p5 ∨ (p4 ∨ (p2 → ((p1 ∨ (False ∨ True)) ∨ p3)))) ∧ ((((p2 ∨ p5) ∨ (p4 ∨ p3)) ∨ p1) ∨ True)) → (p4 ∨ (p4 ∨ (p4 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h8 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h9
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h10 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h11
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h13
          case inr h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h15
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h24 =>
            -- Disjunctions on the left can always be decomposed.
            cases h24
            case inl h25 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h21
            case inr h26 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h21
          case inr h27 =>
            -- Disjunctions on the left can always be decomposed.
            cases h27
            case inl h28 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h28
            case inr h29 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h21
        case inr h30 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h21
      case inr h31 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h21
    case inr h32 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- Disjunctions on the left can always be decomposed.
          cases h34
          case inl h35 =>
            -- Disjunctions on the left can always be decomposed.
            cases h35
            case inl h36 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h37
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h38 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h39
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h40 =>
            -- Disjunctions on the left can always be decomposed.
            cases h40
            case inl h41 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h41
            case inr h42 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h43
              -- True on the right can always be proven directly.
              apply True.intro
        case inr h44 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h45
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h46 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h47
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44478303323945975995933603804 : (((((p3 ∧ p1) → ((p4 → p2) → (p5 → (p2 ∧ (p4 ∨ p1))))) → (((False ∧ False) ∧ p1) → ((p5 ∨ (p3 → p1)) ∧ False))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348535788788116938213957013448 : (p3 → (p3 ∧ (p3 → (((True → (p3 → p5)) ∧ ((p4 ∨ p2) ∨ (p5 ∨ (((p3 ∧ p1) → False) ∨ p4)))) → ((p2 ∨ (p1 ∨ p5)) ∨ p3))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44883685071226863449717645439 : (((((True → True) ∨ p4) → ((p2 → ((p4 ∧ p2) ∧ (p2 ∧ p5))) ∧ (p5 ∧ (True → ((False ∧ ((True → p3) ∧ p2)) ∨ p1))))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317770504794445600901546058283 : (p4 ∨ ((((((((False → p5) ∧ p3) ∧ (p5 ∨ p2)) → (p5 ∧ p4)) ∧ p5) ∧ p2) ∨ ((((p1 ∧ p1) ∨ p2) ∨ (False → p4)) ∨ p4)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86083184569417350849624094094 : (((True → ((p5 → (p5 ∧ (p3 → (p3 ∧ True)))) ∧ False)) ∧ ((p2 → (((p1 → p5) ∨ False) → ((p5 → (p2 → False)) ∨ p5))) ∨ False)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200916327555670383137225127545 : ((p1 ∨ (((p5 ∧ (p1 ∧ p5)) → p5) → p2)) → ((p5 ∧ (p3 ∨ ((p1 → (p4 ∧ ((p3 → (p2 ∨ p2)) ∧ p2))) → p1))) ∨ (False → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147636706152737231141082377208 : (((((p4 → (p3 ∨ True)) → (p3 ∧ (p1 ∧ ((p4 ∧ p5) → (p5 ∧ (p5 → (p1 → p3))))))) → p5) → p3) ∨ ((p5 → p4) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58713524704394249936869158117 : (((p3 → True) ∧ (p2 ∨ ((False ∨ (((True ∨ p4) → False) ∧ ((((((p1 ∨ p5) ∨ p4) ∧ p4) → p2) ∨ p1) ∧ (p4 → p3)))) → p1))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h10 : (True ∨ p4) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h11 := h5 h10
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319378602833018815488671982117 : (p4 ∨ ((p3 ∧ (((((p1 ∨ p5) ∨ (p1 ∨ (True ∨ p5))) → p3) → True) ∨ p3)) ∨ (((((p2 ∨ (True ∨ False)) ∧ p5) ∧ p5) ∨ True) ∨ p5))) := by
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
theorem thm_5_vars_328272953273545019934934549100 : (True → (((p5 ∨ (((p2 → ((True → (p3 ∧ (p4 ∨ (p2 ∧ p4)))) ∨ p1)) ∧ p3) ∨ (p1 ∧ p4))) ∧ False) ∨ ((True ∧ (True ∨ p1)) ∨ p3))) := by
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
theorem thm_5_vars_263075538730333572445732867788 : (True ∧ (((p2 → ((True ∨ (False ∧ (((True ∧ p3) ∧ p1) ∨ False))) ∧ (p3 ∨ ((p4 ∧ ((p4 ∧ p5) ∧ p4)) ∧ p4)))) ∧ p2) ∨ (p2 → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215730859528096019272825888035 : ((False ∨ (p3 ∨ (p2 ∨ p2))) ∨ ((((p3 ∧ (p4 ∨ False)) → (p3 → p2)) ∧ True) ∨ (p1 ∨ (False ∨ (True ∨ ((p4 → (p1 ∧ p5)) → p2)))))) := by
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
theorem thm_5_vars_322429135045893620841922094997 : (p5 ∨ (((((p1 → p3) ∨ True) → (p4 ∨ p1)) ∧ ((p3 ∧ (p4 ∨ (p3 → (p3 ∨ p5)))) ∨ (((p5 ∧ p3) ∧ p1) ∨ (p5 ∨ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116663364048428971356047445631 : (((p4 → p2) ∧ ((p3 ∧ ((False ∨ (p2 ∧ p3)) ∧ (p3 → ((p2 ∧ ((False ∧ (p1 ∧ p2)) ∨ p3)) ∧ (False ∨ p2))))) ∨ p5)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116754264560612947044963518219 : (((p5 ∧ p3) ∨ (p5 ∨ ((p3 ∧ p1) ∨ (((((p5 ∧ p4) → ((False ∧ (True ∧ p3)) → (True ∧ p3))) → p3) → p2) → True)))) ∨ (p4 → p5)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158029309310508398388305572209 : (((p1 ∨ ((p5 ∨ (p4 ∨ p2)) ∨ True)) ∧ (((p3 ∨ p3) → False) → ((p5 ∨ False) → (p1 ∨ True)))) ∨ ((p4 → p4) → ((False ∨ p3) ∧ p1))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_307413511954077924368944461456 : (p1 ∨ (p4 ∨ (p2 → ((((p5 → p1) → p4) ∧ p1) ∨ (((((p2 → False) ∨ False) ∨ (False → True)) ∨ True) ∨ (p4 ∨ ((p2 ∨ p3) ∧ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_401362912545863365837849033526 : ((((((((False → (True ∧ (False ∨ False))) → False) ∧ (p4 ∨ p3)) ∧ (p3 ∨ (((p4 ∧ p3) ∧ (p5 ∨ (p4 ∨ True))) ∧ p2))) ∧ True) → False) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h9 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h10 : (False → (True ∧ (False ∨ False))) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- False on the left can always be used.
        apply False.elim h11
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h12 := h6 h10
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h14.left
      let h17 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h16.left
      let h19 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h20 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h21 : (False → (True ∧ (False ∨ False))) := by
          -- Implications on the right can always be decomposed.
          intro h22
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- False on the left can always be used.
          apply False.elim h22
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h23 := h6 h21
        -- False on the left can always be used.
        apply False.elim h23
      case inr h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h26 : (False → (True ∧ (False ∨ False))) := by
            -- Implications on the right can always be decomposed.
            intro h27
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- False on the left can always be used.
            apply False.elim h27
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h28 := h6 h26
          -- False on the left can always be used.
          apply False.elim h28
        case inr h29 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h30 : (False → (True ∧ (False ∨ False))) := by
            -- Implications on the right can always be decomposed.
            intro h31
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- False on the left can always be used.
            apply False.elim h31
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h32 := h6 h30
          -- False on the left can always be used.
          apply False.elim h32
  case inr h33 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h34 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h35 : (False → (True ∧ (False ∨ False))) := by
        -- Implications on the right can always be decomposed.
        intro h36
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- False on the left can always be used.
        apply False.elim h36
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h37 := h6 h35
      -- False on the left can always be used.
      apply False.elim h37
    case inr h38 =>
      -- Conjunctions on the left can always be decomposed.
      let h39 := h38.left
      let h40 := h38.right
      -- Conjunctions on the left can always be decomposed.
      let h41 := h39.left
      let h42 := h39.right
      -- Conjunctions on the left can always be decomposed.
      let h43 := h41.left
      let h44 := h41.right
      -- Disjunctions on the left can always be decomposed.
      cases h42
      case inl h45 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h46 : (False → (True ∧ (False ∨ False))) := by
          -- Implications on the right can always be decomposed.
          intro h47
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- False on the left can always be used.
          apply False.elim h47
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h48 := h6 h46
        -- False on the left can always be used.
        apply False.elim h48
      case inr h49 =>
        -- Disjunctions on the left can always be decomposed.
        cases h49
        case inl h50 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h51 : (False → (True ∧ (False ∨ False))) := by
            -- Implications on the right can always be decomposed.
            intro h52
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- False on the left can always be used.
            apply False.elim h52
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h53 := h6 h51
          -- False on the left can always be used.
          apply False.elim h53
        case inr h54 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h55 : (False → (True ∧ (False ∨ False))) := by
            -- Implications on the right can always be decomposed.
            intro h56
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- False on the left can always be used.
            apply False.elim h56
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h57 := h6 h55
          -- False on the left can always be used.
          apply False.elim h57
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_551635786496656827534851212441 : (((p1 ∨ ((p2 → p3) ∨ (p1 → (True ∧ (((False ∨ ((True → p4) ∧ p1)) → ((p1 ∨ False) ∧ ((p4 → (p4 ∧ p3)) ∨ p5))) ∨ True))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612601279109392786548787034835 : ((((((((True ∨ p5) → (p1 → ((p4 ∨ p5) → False))) → ((p2 → p1) ∨ ((p4 → p4) → p3))) ∧ (True ∨ p2)) ∨ (True ∧ p5)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_187427015342191666465474870862 : ((p5 ∧ ((((False ∧ False) ∧ False) → True) ∨ ((p2 → p5) ∧ False))) → ((((True → ((p3 ∨ p5) ∨ p4)) → p2) ∨ ((True ∧ False) ∨ True)) ∧ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172609733499267755596418943522 : (((True → (p1 → p5)) → ((((True → (p4 → p1)) ∧ (p1 → p3)) → p5) ∧ p5)) ∨ ((p5 ∨ ((True ∨ p1) → (False ∧ p1))) → (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245585405411567745977226366264 : ((p3 ∧ False) ∨ (((p5 ∨ ((p5 → (((p3 → p5) → False) ∨ (p2 ∨ (((((p4 ∧ p4) → False) ∨ p3) → True) ∧ p3)))) → p4)) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200224818569273713365603269720 : ((((p2 → p3) ∧ True) → ((p2 ∨ False) ∨ p4)) → (((False ∨ ((p5 → p2) → p1)) ∨ (p3 ∨ (p5 ∨ True))) ∧ (False → ((p2 ∧ True) → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111683042283372360259238858701 : (((((p3 ∨ (((p5 ∧ (p3 ∧ (p5 ∧ (((p3 ∧ p1) ∧ (False ∧ True)) → (True ∧ p2))))) ∧ p1) → p5)) ∧ p5) → False) ∨ True) ∨ (True ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54854430723638806113202193530 : ((((((p5 → True) ∧ p4) → True) ∧ True) ∧ ((False ∨ ((p2 → p4) ∧ (p1 ∧ (((True ∧ p2) ∨ p1) → (p5 ∨ (p3 ∧ True)))))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172364005582609912636747456881 : ((((False ∨ p5) ∧ (True ∧ (False ∧ p3))) ∨ ((p5 ∨ p4) ∨ (p3 → (False ∨ True)))) ∨ (p3 → ((p5 → (p4 → p5)) ∨ ((p4 ∨ p5) ∨ p4)))) := by
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
theorem thm_5_vars_158955176863823850484804800738 : ((p2 ∨ (p1 ∧ ((((p2 ∨ p4) ∨ p3) → ((False ∧ (((True ∨ False) ∨ False) ∨ True)) ∧ True)) ∨ p5))) ∨ (p2 → (p5 ∨ (p2 ∨ (p1 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8273917386665002993089494913 : ((((((p5 ∧ ((True → ((p3 ∧ (p5 ∨ (p1 ∨ p3))) ∧ (p1 → False))) ∨ p1)) ∨ ((p3 ∨ (p1 → False)) ∧ p2)) → p5) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63903353834032011060096468098 : ((False ∨ (((p2 ∨ (p5 ∧ (p1 → p1))) ∧ (((p1 ∧ ((False → (p1 → p3)) ∨ p5)) → (p4 → p2)) ∧ ((p4 ∧ True) → p3))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656467179460364930373115481396 : (((((p4 ∧ (True ∧ ((False → p2) ∧ ((p3 ∧ p1) ∧ p4)))) ∨ ((((p2 ∧ (p1 ∨ False)) → False) ∧ (p3 ∧ p2)) → False)) ∨ (False → False)) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720371539925564586655655458721 : ((((((p3 ∧ True) → p1) ∨ p4) → (p5 ∧ (p5 ∨ (((False → p4) → p4) ∧ ((((p4 ∧ p5) ∨ p3) ∨ ((p2 ∧ False) ∧ p1)) ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257410662328545524657965175006 : ((p2 ∨ p5) → (False ∨ ((p3 → p1) ∨ ((((((((p3 ∨ p5) ∧ (p5 ∨ p1)) ∧ p5) ∧ p3) ∨ ((p4 ∧ p2) ∧ False)) ∧ p3) ∧ p5) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323810557687945073247847279296 : (p5 ∨ ((True → ((p1 ∨ ((p5 → (False ∨ p1)) → (((p3 ∧ False) → True) → (p3 ∨ False)))) ∧ p2)) ∨ ((p1 ∧ (False ∧ p1)) → (p1 ∨ p4)))) := by
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
theorem thm_5_vars_41628459909458564977457751717 : (((((p4 ∨ (p1 ∨ p1)) ∨ ((p1 ∨ p3) ∨ p4)) → ((p2 ∧ ((p3 ∧ p3) ∨ ((p3 ∨ p5) ∧ p4))) ∨ ((p2 → p2) ∨ p5))) ∨ p1) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h7
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- One of the premise coincides with the conclusion.
        exact h9
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
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h15
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h17
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351823648836878170635766223990 : (p4 → (((p2 ∨ (p4 ∧ p2)) → ((p2 → (False ∨ (p1 ∨ p5))) → p1)) ∨ ((False ∧ (p5 ∨ ((p2 ∨ p5) ∧ p1))) ∨ (p4 → (True ∨ p2))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134957551224330779024994453533 : ((((p1 ∧ ((p5 → (p2 ∨ ((False → True) ∨ p4))) → (False ∨ p5))) → ((p2 ∨ (p4 ∨ True)) ∧ p4)) ∧ (True ∧ False)) ∨ ((p3 ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664656563757693323309117849763 : ((((True → (p5 ∧ ((p5 → p1) ∧ (p5 ∧ ((p4 ∧ (((p3 → p1) ∧ (p1 ∨ (False → (p4 ∧ True)))) → p1)) → p5))))) → (False ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40782392001178008646168130945 : ((((p2 ∧ (((p1 → p1) → (True ∧ ((False ∨ (p1 ∨ (((p3 ∨ p4) → (p5 → p5)) → (p1 ∧ p1)))) → p3))) ∧ p2)) → p4) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671237122070973539741296837956 : ((((p4 ∨ ((p3 ∨ (((((p2 ∨ (p2 ∨ p5)) ∧ p3) ∧ p3) ∨ ((p3 → p4) → p1)) ∧ p3)) ∨ (p5 ∨ True))) ∨ ((p2 ∧ p3) ∧ p1)) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111031058205515745663820630004 : ((((((((p5 → False) ∨ (p4 → (p3 → (p4 → (p1 ∧ p3))))) ∧ p5) ∨ p4) ∨ False) ∧ ((True ∧ (p1 ∨ p3)) → True)) ∧ p5) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124347256926551370274649330142 : (((((True → p2) → (p5 ∧ (True ∧ p2))) ∧ p3) ∨ ((p1 ∧ ((p4 ∨ False) → (False ∨ ((False ∧ p3) → (p3 → p1))))) ∧ p4)) → (p2 → p2)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614547941329655194478603062517 : ((((((True ∧ ((p2 ∧ p3) → (p2 → p2))) ∧ (p2 ∧ ((p1 → (p1 ∧ p3)) → (True ∧ False)))) ∧ (False ∨ (p2 ∨ (False ∧ p4)))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_683261563852466914720278786199 : ((((p1 ∨ (((True ∨ p4) → (p4 ∧ ((False ∧ False) ∧ (p2 ∧ p1)))) ∧ (p1 ∧ (False ∨ True)))) ∧ (((p4 ∧ (p3 ∨ p2)) ∧ False) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715669575253152146969472529868 : (((((p4 → (False ∨ True)) ∧ p1) ∧ ((p4 ∧ (((((p1 ∨ False) ∧ p1) ∨ (p5 → ((p2 ∨ p5) → p3))) → p5) ∧ p2)) ∨ (p2 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173146303861244115060211175639 : ((p3 ∨ ((((p2 ∧ ((False → False) ∧ p2)) ∨ False) ∧ False) ∧ (True ∧ (p3 ∧ False)))) ∨ ((True ∨ (p4 → True)) ∨ ((True → (False → p1)) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41341040794481907445772837304 : (((((((True ∧ p5) ∨ ((True ∧ p3) → False)) ∨ p4) → (((p2 ∧ p2) → False) ∨ p1)) ∨ (p3 ∧ (p4 ∧ (p3 → (True → p1))))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798497649454840792359859764787 : (((p1 → (((False ∨ (p3 → True)) ∨ ((p2 ∧ p1) ∧ True)) ∧ (False ∧ (((p5 → True) → p5) → ((True → p3) ∧ ((p4 ∨ p4) ∧ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208447655470215099498539323666 : (((False → False) ∨ ((p2 ∧ p2) ∨ True)) → ((True ∧ True) → ((((True ∨ (p3 → True)) ∧ p3) ∧ (p3 ∧ ((p4 → p3) → True))) ∨ (p1 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197453444797998699645214565994 : ((((p1 → (p4 ∨ p3)) ∨ p1) ∧ (False ∧ False)) ∨ (False ∨ ((p3 ∨ ((p4 ∧ (((True ∧ (p2 → p2)) → p4) ∧ (p5 ∧ p2))) → p4)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148147138834132191925048994235 : (((p1 ∨ ((((p1 → p3) → ((((p1 ∧ (p1 → p4)) ∧ p3) → p4) ∧ False)) ∨ p2) → p4)) → (p3 ∧ p2)) ∨ (((p1 ∧ p3) ∨ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190753581357932647301148745873 : (((p5 ∨ (p2 ∧ (False ∨ (True ∨ p4)))) ∧ (p5 ∧ p1)) ∨ ((((p2 → p2) ∨ p3) → (p4 ∨ (True → (False ∨ False)))) → (p4 ∨ (True → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 → p2) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149554197016100823913073821816 : ((p2 ∧ ((p4 ∨ ((p2 ∨ p5) ∨ (p1 ∨ ((p2 → False) ∨ p2)))) → ((p1 → (False ∧ p4)) ∧ (p5 → p4)))) ∨ ((True ∧ (True ∨ p3)) ∨ p3)) := by
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
theorem thm_5_vars_748521033353834887380033814294 : ((((p3 → True) → (((p3 → p5) ∨ p2) ∨ (((((((p2 ∨ (p4 ∨ p1)) ∨ p2) ∨ p4) ∨ (False ∨ p1)) ∨ p2) ∧ p1) ∨ (p4 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233068617548867503394159670514 : ((p4 ∧ (p4 ∨ True)) → (False ∨ ((((p3 ∧ False) ∨ p2) ∧ p2) → (((True ∨ p5) ∧ ((p4 ∨ p1) → False)) ∨ ((p5 ∧ (p4 → True)) → p4))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258602767720655727372655026179 : ((p5 ∨ p4) → ((((p3 ∨ (p3 ∨ False)) → (p2 ∨ (True ∧ False))) ∧ ((False ∧ p2) ∧ True)) ∨ (((p1 ∧ p4) ∨ ((False → p4) → p1)) ∨ True))) := by
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
theorem thm_5_vars_232493717401134684575441720246 : ((True ∧ (True → p5)) → ((p1 ∧ (p2 ∧ ((p4 ∧ (p3 ∨ p1)) ∨ ((True ∨ (((p1 ∧ (True → p1)) ∨ False) ∧ (False ∧ p3))) ∧ p1)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217392173443330763232781481545 : (((True → (True ∨ p5)) ∨ p4) → ((((p3 ∨ (p3 ∧ ((((p5 → p3) ∨ p3) → p1) ∧ (True ∧ p1)))) → False) ∧ (p4 ∨ p2)) → (p1 ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
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
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42382935377468235191825806266 : (((p4 ∧ ((p2 → (((p5 → True) ∧ (p2 ∧ (p2 → False))) ∧ ((p2 → True) → ((p3 ∧ True) ∨ p5)))) ∨ (False ∧ (True ∨ p4)))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175519172891889348493557595249 : ((p4 → ((p5 ∧ (((((False → (p1 → p1)) → p5) ∨ p2) → False) → p1)) ∧ p1)) → (p4 ∨ ((((True ∧ p4) → p3) ∨ p3) ∨ (True ∨ p1)))) := by
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
theorem thm_5_vars_118453969991177700177851798129 : ((p3 ∨ ((((p5 ∧ p3) ∨ (((p2 ∨ ((p1 ∧ (((p5 ∨ (True ∧ True)) ∧ p5) ∧ p4)) ∧ p3)) ∨ p1) ∧ p5)) ∧ p5) ∨ p3)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204916832756829400129396676491 : ((((False ∨ False) ∨ (False → True)) → p1) ∨ ((((False → p3) ∧ p1) ∧ (p1 → (False → p1))) → ((p4 ∧ ((p3 → (p5 ∨ True)) ∧ p5)) ∨ p1))) := by
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
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337718464234272251261335280879 : (p1 → ((p1 → (p4 ∧ (((p2 → (((True → p5) → (False ∨ p3)) ∧ p2)) → (p3 ∨ False)) ∧ p5))) → (((p4 → False) ∧ True) ∨ (p3 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241387528945350969483183473920 : ((False → False) ∧ (p5 → (((p3 ∨ (p5 ∨ ((p2 → False) → p5))) ∧ p4) ∨ ((((p5 → True) ∧ (p3 → p4)) ∧ True) ∨ (p4 ∨ (p1 ∨ p5)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117064044430292647421343896578 : (((p5 ∨ p4) → ((p4 ∨ p2) ∧ (p2 ∧ (((p1 ∧ ((p5 → p4) ∧ (True ∨ p5))) ∧ (False → ((p5 → p5) → p4))) → p5)))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88174462099774220359850631064 : ((((False ∨ True) → (p3 ∧ False)) ∧ ((True ∨ ((p3 ∨ p5) → p1)) → ((False ∨ p4) ∨ (p5 ∨ (p5 → ((False ∧ (p4 ∧ p3)) ∨ p2)))))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706580533587585694929297748349 : ((((p1 → ((p5 → (p5 ∧ (False ∧ p3))) ∨ False)) ∧ (((True ∨ p3) ∧ (((False → (p4 ∨ p1)) ∧ (p5 ∨ p5)) → True)) → (p3 ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51373551553758749680463399833 : (((((True → ((p5 ∧ (p3 → (((p4 ∧ (p3 → p4)) ∨ p2) ∨ p2))) ∧ p5)) ∧ p3) ∨ p1) → ((((p1 ∧ p4) ∧ p5) ∨ True) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111677647165326555077181654001 : ((((((((p1 ∨ (p1 → p3)) ∧ (p2 ∧ ((True ∨ ((p4 ∨ p3) → p3)) ∧ p2))) ∧ (p1 → p2)) ∨ False) ∧ True) → p4) ∨ True) ∨ (True ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18951422358122046937639285483 : (((p3 ∨ (p2 ∧ (p5 ∨ (p2 ∨ (True ∧ ((True ∨ (True → ((False ∧ p1) ∧ p1))) ∧ p5)))))) ∨ (((False → False) ∨ p2) → (p1 ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263812496312544264193082083491 : (True ∧ ((p3 ∨ ((p2 ∨ ((False ∧ p2) ∧ True)) ∨ (p4 ∨ ((p2 ∧ (p5 → p5)) ∧ p5)))) ∨ (p3 → (p3 ∨ (True → (p5 ∨ (p1 → p3))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



