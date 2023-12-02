variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663805448070100514268204636445 : ((((p2 ∧ (p3 ∧ ((p4 ∨ (p4 ∧ ((((((p2 → p5) ∧ True) → p4) → (p2 ∨ p1)) ∨ p3) ∨ (p1 ∧ False)))) → False))) → (p1 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260344842936530527890197998606 : ((p2 → p5) → (((p4 ∧ p4) ∧ (((p1 → ((((True → (False ∧ True)) ∧ ((p1 → p3) ∨ p2)) → p3) → (p2 ∧ False))) ∨ True) ∨ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315821352109182225345065496047 : (p3 ∨ ((p3 ∨ p4) → (p2 ∨ (p1 ∨ (p1 ∨ (((p3 ∧ (p3 ∧ p5)) → (((p2 ∧ ((p1 ∨ (p4 ∧ p3)) ∨ p4)) → p4) ∧ p4)) ∨ p3)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h4.left
        let h11 := h4.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h4.left
        let h18 := h4.right
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h4.left
      let h23 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- One of the premise coincides with the conclusion.
      exact h21
    -- Conjunctions on the left can always be decomposed.
    let h26 := h4.left
    let h27 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h28 := h27.left
    let h29 := h27.right
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699533011104875889431846906655 : (((((False ∨ (p2 ∧ (p1 → ((p1 ∨ True) → (p4 ∧ True))))) ∨ p2) → (((((p2 ∨ (p4 ∨ p5)) ∧ (p5 ∧ True)) ∨ p1) ∨ p4) ∨ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207018194091652183547804292397 : ((((p1 → False) ∨ (p1 ∨ p5)) ∧ p5) → (False ∨ ((p1 ∨ ((True ∧ (((p1 → (False → (False → (p3 ∧ p1)))) ∨ p4) ∨ p2)) ∨ False)) ∨ True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
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
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673093598491284840482029586001 : (((((((p1 ∧ (p4 ∧ (p3 ∧ (p1 ∧ (False ∧ p2))))) → p5) → False) ∨ ((((p1 ∨ p2) ∧ p4) ∨ p3) ∨ False)) → ((p5 ∨ p2) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775522998136295256490680606156 : (((False ∨ (p5 ∧ ((((((p5 → p3) ∨ True) → p5) ∧ (p2 ∨ (False ∨ (((p5 ∨ ((p2 ∧ p5) ∧ p4)) ∨ True) ∧ p4)))) → p1) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121361485357356423529707545115 : (((((((((((((p4 ∨ p5) → p4) ∨ p4) ∧ p3) ∧ (p2 ∨ p3)) ∨ (False ∨ True)) ∧ True) ∨ True) ∨ True) ∨ p2) ∨ True) → p3) → (p4 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((((((((((p4 ∨ p5) → p4) ∨ p4) ∧ p3) ∧ (p2 ∨ p3)) ∨ (False ∨ True)) ∧ True) ∨ True) ∨ True) ∨ p2) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149106373650270694108835274012 : (((p2 → (p5 ∧ p4)) → ((((((p1 ∨ p5) ∧ p3) ∧ (False → p3)) ∧ p5) ∧ ((p2 → p4) ∧ p1)) ∨ True)) ∨ (p3 → (p1 → (True → p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299257900657172967611453892660 : (False ∨ ((((((True ∨ p2) ∨ p1) ∧ p2) → (((False → True) ∧ ((p3 ∧ p2) ∧ (p5 → False))) ∨ True)) ∨ (p4 ∨ (p3 ∨ (p5 ∨ p2)))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h2
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
theorem thm_5_vars_646708440508753051533754276515 : ((((p2 → (((((p1 → p2) ∧ p5) → ((p2 → (False ∧ (p1 → False))) ∨ (p1 → (p4 ∧ (p2 ∨ p1))))) → (p4 → False)) ∨ True)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187052084881215539195982067175 : (((p5 ∧ True) ∧ ((p2 → (p3 ∧ (p2 ∨ p5))) ∧ (p1 ∧ p4))) → (p2 ∨ (((False ∨ (p3 ∧ ((p2 ∧ False) ∨ p1))) ∨ (p5 ∨ False)) ∧ p4))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149708313879810771351311191737 : ((p5 ∧ (p4 ∧ (((((p4 ∧ ((p5 ∧ p1) → ((p2 ∧ False) → p4))) ∧ (p2 ∨ p5)) → p3) ∧ p5) ∧ False))) ∨ (True ∨ ((True → p5) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322602470850745657820003041293 : (p5 ∨ ((p2 → ((True → (False ∧ p1)) ∨ ((p1 ∨ ((((p3 ∨ (p4 ∧ p4)) ∨ ((p3 ∧ True) → True)) ∨ (p4 ∨ p4)) ∧ False)) ∧ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356024439729006604749147862641 : (p5 → (((p4 → ((p2 ∨ (((((p3 → p4) → (False → p3)) → p2) ∧ False) ∧ p4)) → p5)) → (p4 ∧ p3)) ∨ (p2 ∨ (p5 ∨ (p2 → p5))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44289354530703014679777097321 : (((((p2 → (True ∨ ((p1 ∧ (p2 ∨ p5)) ∨ ((False ∨ p5) → p2)))) → (p1 ∧ False)) ∧ ((p2 → p1) ∧ (False → (p4 → p5)))) → p5) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (p2 → (True ∨ ((p1 ∧ (p2 ∨ p5)) ∨ ((False ∨ p5) → p2)))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803802810818043387750905889712 : (((p3 → ((((False ∧ p5) ∨ ((False → p3) ∧ ((True ∨ ((p4 ∧ p4) → (p3 → ((p4 ∧ p5) ∧ False)))) → False))) ∨ p2) ∨ (p2 ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40938236099778035847941033433 : (((((p2 ∧ ((True → ((p2 ∨ p2) ∧ p5)) → ((((False ∨ (p5 ∧ p5)) ∨ p1) → (p4 ∧ p3)) ∨ True))) ∨ True) ∨ (p4 ∧ True)) ∨ p4) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158218780329179056055390700496 : (((p2 ∧ (False ∨ p4)) ∧ ((p5 ∨ (((p4 → p1) ∨ p4) ∧ p5)) → (p2 → ((True → p2) → False)))) ∨ (True ∨ (((p1 ∨ False) → True) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8007015819465180794710398727 : (((((p2 ∧ ((p5 ∨ (p1 → False)) → (p2 → ((((p3 → p2) ∧ False) → (False ∧ p2)) → ((p3 ∨ True) ∨ True))))) → p3) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356247999281197321354578661856 : (p5 → (((p2 ∨ ((p2 ∨ p3) ∨ ((p5 ∧ p2) ∧ (p2 ∨ ((p3 ∨ p5) ∨ p3))))) ∧ False) ∨ ((False → p4) ∨ ((p1 → (True ∧ p3)) ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171577257378922156945129801591 : ((((p2 ∨ (True → ((p4 ∧ p4) ∨ ((p1 → p2) ∧ False)))) ∨ (p3 ∧ False)) ∨ p1) ∨ (p1 → ((p1 ∨ p4) → ((False ∨ True) ∧ (p1 → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258782926602588684131431895406 : ((True → False) → (((((True → (((p4 → p3) ∧ p2) → (False ∨ p1))) ∧ p1) ∨ False) ∧ (True ∨ True)) ∧ ((p3 → (p1 → True)) ∨ (True ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350189727904339792513066916052 : (p4 → (((p3 → (p2 → (True → p3))) → (p2 ∨ (((((p5 → ((p5 → (p3 ∧ True)) ∧ p1)) ∨ p3) ∨ (p5 ∨ p2)) → p5) ∧ p1))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59336119424871221394177037124 : (((p4 ∨ p5) ∨ ((((p1 → p2) → p4) → p1) ∨ (p1 → ((p3 ∧ True) ∨ (((p5 ∧ ((p1 → p4) ∨ p3)) ∧ (p2 → False)) → p1))))) ∨ p4) := by
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134424084583765994972863142503 : (((p4 → (((((p4 → p1) ∨ (((True ∨ (p2 ∨ False)) ∧ True) → p5)) → (False ∨ p1)) ∨ (True → True)) ∨ p1)) ∨ False) ∨ ((p4 ∨ p5) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_37176722112829049313281911423 : (((((((True → (p2 ∨ p4)) ∧ ((p1 ∧ p5) ∧ p4)) ∧ (False ∨ p1)) ∨ ((p2 ∧ p2) → (p1 ∨ ((p2 → p2) ∧ p4)))) ∧ p4) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21017629749172350984004243908 : (((((p5 ∧ (((False ∨ False) ∧ p5) ∨ p1)) ∨ (p2 ∧ p2)) → p5) → ((((p4 → (False ∨ True)) ∧ (p4 → (p3 ∧ False))) ∧ p4) → p3)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48053141252426957540287123402 : (((((False ∨ p2) ∧ ((p2 ∧ (p1 ∨ p5)) ∧ p2)) ∧ ((True → p1) ∨ (p1 ∧ ((p4 ∨ (p4 ∨ (False → True))) ∨ p1)))) → (p4 ∨ p1)) ∨ False) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h5.left
    let h9 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h18
          case inr h19 =>
            -- Disjunctions on the left can always be decomposed.
            cases h19
            case inl h20 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h20
            case inr h21 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h15
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h22
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h24 =>
        -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
        have h25 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h24, we can now drive its conclusion.
        let h26 := h24 h25
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h26
      case inr h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- Disjunctions on the left can always be decomposed.
          cases h30
          case inl h31 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h31
          case inr h32 =>
            -- Disjunctions on the left can always be decomposed.
            cases h32
            case inl h33 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h33
            case inr h34 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h28
        case inr h35 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351009901225422542232129201463 : (p4 → ((p5 ∨ (p1 → (((p3 ∨ ((p5 → (True → False)) → ((p2 ∧ p2) → (p3 ∧ p1)))) ∨ p5) ∧ (True ∨ (p4 ∧ False))))) ∨ (False → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702136336002255228971976593255 : ((((p4 → (((p2 ∨ p3) ∨ False) ∨ (True → (p1 → False)))) ∧ ((True ∧ ((p2 ∧ (((p4 → p3) ∧ p5) ∨ p5)) ∨ (p5 ∧ p4))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41434202228372514963177440936 : (((((p3 ∧ (((True → p3) ∧ p1) ∧ (p3 ∨ p3))) → ((False → p4) ∧ False)) → ((p5 ∨ ((p3 ∨ (True → p1)) ∨ True)) ∨ p5)) ∨ False) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_40067999115438478750022782150 : (((((p5 ∧ (((p3 → ((True ∧ (False → (p4 ∨ (p5 ∨ p5)))) ∨ p4)) → (False ∨ (p3 ∧ (p1 → p5)))) → p5)) ∨ p2) ∧ p1) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114054960077984404084402268564 : ((((True ∨ ((True → p1) → (p5 ∧ ((p1 → (p4 ∨ (False ∨ True))) ∧ p2)))) → (p3 ∨ (p1 ∨ p3))) ∨ (False ∧ (p1 ∨ p4))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620547411835994662919088096572 : (((((p3 → False) ∨ ((p1 ∧ (p4 ∨ (p4 → ((p2 ∧ p3) ∨ ((p4 ∨ p4) ∧ (p1 ∨ p3)))))) → (((p3 ∧ p3) ∨ True) ∨ True))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_124792763984726704797125760564 : (((p3 → (True ∨ (p1 ∨ p1))) ∧ ((((p3 ∨ False) → (p5 → p2)) ∧ ((False → p5) → p2)) → (p1 ∧ ((False ∨ p5) ∧ p1)))) → (p2 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (((p3 ∨ False) → (p5 → p2)) ∧ ((False → p5) → p2)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h11 := h4 h5
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h14 =>
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745214341770086563320356879125 : ((((p5 ∧ True) → ((p5 ∨ (p3 ∧ p5)) ∧ (p1 ∨ (p3 → (((False → ((True ∧ p1) ∧ p5)) → (p1 ∧ p5)) ∨ ((True ∨ p1) → p5)))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111046174366901233820373623524 : ((((p4 ∧ ((False ∨ p3) ∨ (True ∨ (((((p4 → p2) → True) ∧ False) ∨ p3) ∨ p5)))) ∨ (p1 ∨ (True ∧ (False → p5)))) ∧ p5) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46923180710534571078481773440 : (((((p3 ∧ (p1 → True)) ∧ ((((((p2 → False) → p5) ∨ p3) ∧ (p5 ∧ (p4 → p4))) ∧ p2) ∨ (False → p2))) ∨ p1) ∨ (True ∨ p3)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181008188961505695750520986639 : (((p1 ∨ p2) ∨ ((((True ∨ p5) → (p3 ∧ p4)) ∧ p2) ∧ (p2 ∨ p4))) → (p4 ∨ (((p5 ∨ (p2 ∨ True)) → ((False ∨ p1) ∨ p3)) ∨ p2))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h8 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57366909367048885585568315140 : (((p4 ∧ (p3 ∨ p1)) ∨ (((p1 ∨ p1) ∨ ((True ∨ ((p2 ∧ True) ∧ p5)) ∨ ((p5 ∨ p1) ∨ (True ∧ p5)))) ∨ (p4 ∧ (p4 ∨ p2)))) ∨ p5) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134181473895299925184495980813 : (((((p2 ∨ p5) ∨ ((((p4 ∧ p1) ∨ (p5 ∨ False)) → False) ∨ True)) ∧ (((True → False) → p2) ∨ (p3 ∨ p2))) ∨ False) ∨ ((p1 ∨ p1) ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40537689186467703402657883894 : ((((p3 ∨ (((((p5 → p2) → p2) ∧ p4) ∧ ((False ∧ (p3 ∧ p4)) ∨ p4)) ∨ ((p2 ∧ (False → p3)) ∧ (p1 ∨ True)))) ∨ True) ∨ p2) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805385105955634832860289598394 : (((p3 → (False ∨ (p2 ∨ (True → ((p2 ∧ p2) ∨ ((((p4 → p1) → (p4 ∨ p2)) ∨ (p3 ∧ (True ∨ p5))) ∧ ((p3 ∨ False) ∨ p3))))))) ∨ p4) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114615537208285638952393904924 : (((p3 → ((((p4 → (p4 ∧ p4)) → (p2 ∧ (p4 ∨ (p2 ∧ True)))) ∧ p1) → False)) ∧ ((True ∧ (p1 ∧ p4)) ∧ (p1 ∨ True))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607001289535464551546820525349 : (((((((((p2 ∧ p3) ∨ (p1 → p4)) ∨ p5) → (p2 ∧ ((True ∨ p2) ∨ p5))) → (((True ∨ (False ∨ True)) ∧ False) ∧ False)) ∧ p2) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_233918177057175803464014196179 : ((p4 ∨ (p1 → False)) → (((((p1 → (True → (False ∨ p1))) ∧ ((True ∨ p5) ∨ (p5 ∧ True))) → True) → p1) ∨ (((True → p4) ∨ p1) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h10 := h8 h9
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h12 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h13 := h6 h12
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156935361190170631372290586789 : ((((p4 ∨ ((((p1 → (True → p2)) → True) ∧ p2) → ((p2 → p3) ∧ p4))) ∧ (True ∧ p4)) ∨ p3) ∨ ((True ∨ p5) ∧ ((p3 → True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351916616177458759533849297537 : (p4 → ((p1 ∧ (False ∧ (p4 ∧ (p3 ∨ (p3 ∨ (p2 ∧ p3)))))) ∨ ((False → (p4 ∧ (p5 → p2))) ∨ ((True → p3) ∨ ((p4 → False) → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115962982291640546616794902109 : (((p5 → (p3 → (p1 → p2))) ∨ (True → (((True ∧ p1) ∧ (((p4 → True) ∨ (False ∧ False)) → (p2 ∧ p4))) ∧ (p1 ∨ p3)))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199094217547947333093278027765 : (((((p3 ∨ p1) ∧ p3) ∧ (p1 → p1)) ∧ True) → ((p3 → p2) ∨ ((((p3 ∧ p4) → (p4 → False)) → p1) ∨ (p3 ∨ (True → (p4 ∧ p1)))))) := by
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
  cases h6
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184080282590331015268765332254 : (((((p4 ∨ False) ∨ (p3 → p1)) → (p2 ∧ (p3 ∧ False))) ∨ False) ∨ ((True ∨ ((False → (((p3 → (True ∨ p4)) ∧ p2) ∨ False)) ∧ True)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248426206232178850450801907821 : ((p2 ∨ p4) ∨ (p5 ∨ ((((((p1 ∧ (((p2 ∨ p5) ∧ ((False ∧ (p3 ∨ p3)) → p2)) → p1)) ∧ p2) ∧ (p4 ∧ False)) ∧ p1) ∧ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311955289847342341568127771284 : (p2 ∨ (p3 ∨ (((p3 ∨ p2) ∧ p2) ∨ (p2 → ((p1 → True) ∨ (p3 ∨ (((p5 ∨ p2) ∧ p2) ∧ ((False → (True → (p3 ∧ p5))) → True)))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251016214862159683839651486505 : ((p1 → p5) ∨ ((p5 → (((p3 → p3) ∧ p5) → (False ∧ p5))) → (((p3 → p5) ∧ (p2 → True)) → ((p4 ∨ (True → p1)) ∨ (True ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172345217849115785369751459870 : (((p5 ∨ ((p3 ∧ (p5 ∨ p1)) ∨ True)) ∧ (True → (p2 → (True → (p5 ∧ p3))))) ∨ (((p1 ∧ p5) → (p1 ∧ False)) → ((p5 ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3223259875379785285128705317 : ((False ∨ p5) ∨ (((((p5 ∨ ((p4 ∨ True) ∧ ((p1 → p4) ∨ p4))) ∧ p2) ∨ p2) ∧ p1) ∨ (p2 → ((False ∨ (True ∨ p1)) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_117722331933238147622720833596 : ((p3 ∧ (p5 ∨ (p1 ∧ ((p1 ∧ p2) ∧ (((((False ∨ (p1 → p5)) ∧ p4) → p2) ∨ False) ∧ (False ∧ (False → (True ∧ False)))))))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350239316633587116378221490833 : (p4 → (((p1 → p2) → (p4 ∧ ((p5 ∧ p4) ∨ ((p1 ∧ (p2 ∨ (((p2 ∧ False) ∨ p4) ∧ ((p1 ∨ (p3 ∧ p1)) → False)))) ∨ p3)))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64480890296946678634696365747 : ((p1 ∨ (((((False ∧ p1) ∧ (p4 ∧ (p5 ∧ True))) ∨ ((False → p1) ∨ (p2 ∧ (p1 ∧ p1)))) ∨ p5) ∨ (((True ∧ p2) ∧ p1) → p3))) ∨ p4) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623436693504107863401377307644 : ((((False ∨ ((p1 ∨ ((p1 ∧ ((True → True) ∧ (((True ∧ (((p4 ∨ p3) ∨ p1) → True)) ∧ p4) ∨ p2))) → (p2 ∧ True))) → p5)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48620191625443886948151501675 : ((((False → ((p2 ∧ (False → (p1 ∨ ((p3 ∧ (((p3 → p5) ∨ True) → p2)) ∧ p3)))) → p3)) → (False ∨ p1)) ∧ ((True ∧ False) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183786788390725247078682534339 : ((((p3 ∨ ((False ∨ p4) ∧ ((p5 ∨ p3) ∨ p2))) ∧ False) ∧ p1) ∨ (((p2 → (p1 ∨ (False → p2))) → p2) ∨ (p3 → (p3 ∧ (p2 → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118172487880982440701618955895 : ((False ∨ ((p2 → p1) → (p3 ∨ ((p2 ∧ (((p3 → ((p3 ∧ ((p4 ∧ False) ∧ (False ∧ p4))) ∧ p3)) ∧ True) ∧ False)) ∨ p4)))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302498217120406827262613965589 : (False ∨ (False ∨ ((((((p5 → p3) ∧ p1) ∧ p1) → p1) ∧ ((p4 → ((((p5 ∨ p1) ∨ p1) ∨ (True ∧ (p4 ∨ p4))) ∧ p5)) ∨ True)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157112848118939168568926565958 : (((p5 → (((p1 ∨ p5) → (((p5 ∧ p4) ∨ p5) ∨ p2)) → ((True ∧ p4) ∧ (True ∧ p3)))) ∨ p4) ∨ (False → ((True ∨ (p2 → p3)) ∧ p2))) := by
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
theorem thm_5_vars_44679338650664173516511970323 : (((((p3 → p5) ∧ ((False → p5) ∨ p5)) → ((True → (p5 ∧ (p4 → True))) ∨ (((False → (p3 → p5)) ∨ (p1 ∨ True)) ∧ p5))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206433141964409568433437811350 : ((p4 ∨ ((p3 ∨ (p4 → p5)) ∧ p1)) ∨ (p2 → (p2 → ((((True ∨ p4) → (p4 ∨ (p5 ∨ p4))) ∨ p2) → ((p5 ∨ (p4 ∨ p4)) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653098446225414607969292589155 : ((((True → (p5 → (((p1 ∧ (True ∧ True)) → (((p3 ∨ p1) → p3) ∨ (p4 ∨ (False ∧ p4)))) ∨ ((False ∨ p3) ∨ p1)))) ∧ (p3 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164700225746558174868515023012 : (((((((True ∨ p5) ∧ p4) ∧ (False → p2)) ∧ (p1 ∨ (p3 ∨ (True ∧ False)))) ∨ p4) ∨ True) ∨ (((False ∨ p5) ∧ p1) ∨ ((True ∧ p1) ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78378010321952351042638965180 : (((((p5 ∧ ((p4 ∨ p5) ∨ p1)) ∧ (((p2 → (False ∨ p5)) → ((p4 ∧ (p1 ∧ p2)) ∧ (p2 → False))) ∧ p5)) ∧ p4) ∧ (p3 ∧ p3)) → p2) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h7.left
      let h13 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h3.left
      let h15 := h3.right
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h16 : (p2 → (False ∨ p5)) := by
        -- Implications on the right can always be decomposed.
        intro h17
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h18 := h12 h16
      -- We need to get the left conjuct of h18 based on <expert-advice>.
      let h19 := h18.left
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- We need to get the right conjuct of h20 based on <expert-advice>.
      let h21 := h20.right
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h7.left
      let h24 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h25 := h3.left
      let h26 := h3.right
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h27 : (p2 → (False ∨ p5)) := by
        -- Implications on the right can always be decomposed.
        intro h28
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h24
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h29 := h23 h27
      -- We need to get the left conjuct of h29 based on <expert-advice>.
      let h30 := h29.left
      -- We need to get the right conjuct of h30 based on <expert-advice>.
      let h31 := h30.right
      -- We need to get the right conjuct of h31 based on <expert-advice>.
      let h32 := h31.right
      -- One of the premise coincides with the conclusion.
      exact h32
  case inr h33 =>
    -- Conjunctions on the left can always be decomposed.
    let h34 := h7.left
    let h35 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h36 := h3.left
    let h37 := h3.right
    -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
    have h38 : (p2 → (False ∨ p5)) := by
      -- Implications on the right can always be decomposed.
      intro h39
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h35
    -- We have shown the premise of h34, we can now drive its conclusion.
    let h40 := h34 h38
    -- We need to get the left conjuct of h40 based on <expert-advice>.
    let h41 := h40.left
    -- We need to get the right conjuct of h41 based on <expert-advice>.
    let h42 := h41.right
    -- We need to get the right conjuct of h42 based on <expert-advice>.
    let h43 := h42.right
    -- One of the premise coincides with the conclusion.
    exact h43



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199392170817444057883267784625 : ((((True ∧ True) ∧ (p3 ∨ (p4 ∨ p5))) ∨ p4) → (p3 ∨ (True → ((((((True ∨ (False → p5)) → p5) → p1) → (False ∨ p1)) ∨ False) ∨ True)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174076458251351118064376394995 : ((((p1 ∨ (p2 ∧ (((p4 → p1) ∧ p3) → (p4 → p5)))) ∨ p2) ∧ (p5 ∨ p5)) → ((p3 ∨ p3) → (((p2 ∨ p5) ∧ (p2 ∨ p1)) ∨ p3))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
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
        cases h5
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h1.left
    let h20 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h18
      case inr h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h28 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h29 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h18
    case inr h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h31 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h32 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308527733946704608196387982418 : (p2 ∨ (((((False ∨ ((p2 ∨ p3) ∨ p1)) ∧ (((p5 ∧ p2) → False) ∨ p4)) ∧ p1) → (True → ((((p3 ∧ p1) → p4) ∧ p4) ∨ True))) ∨ p4)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
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
        cases h6
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164889638563337454129676417758 : (((p4 → (((False → p2) → ((False ∨ p4) ∧ (p1 ∨ (p4 → p2)))) ∧ (True ∨ p4))) ∨ p4) ∨ ((((False ∧ (p1 ∨ p1)) → True) ∨ p2) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191560120218642043438353844610 : ((p1 ∧ (True → ((p3 → ((p2 ∨ p4) ∧ p3)) ∧ p4))) ∨ ((p3 ∨ ((False → ((p4 → p4) → p1)) ∨ p2)) ∨ (((p1 ∨ p5) ∨ True) → p3))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117581974239153549363793745812 : ((p2 ∧ ((p1 → p4) → (p5 ∧ ((p3 → (((p1 ∨ p4) ∨ (p5 → (p4 ∧ p5))) ∧ ((True → p4) ∨ True))) ∧ (True → p1))))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225882551039867577330439601686 : (((p1 ∧ False) ∨ False) ∨ ((p2 → (((True ∨ ((p2 ∨ p1) ∧ True)) → True) → ((p5 ∧ p5) ∨ ((p1 ∧ ((p1 ∧ p2) → p1)) ∧ p4)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663774557454195183863410885775 : ((((p2 ∧ ((True ∧ (p3 ∧ (((p1 ∧ p1) ∨ p3) ∧ (p1 ∨ ((True ∨ (True → p5)) ∨ False))))) ∧ (p3 ∨ (False ∧ p5)))) → (p1 ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197540354290509239477687659272 : (((((p3 ∧ p4) → False) ∨ p1) ∨ (p4 ∧ p1)) ∨ (((p3 → (True → p4)) ∧ p4) ∨ ((p2 → ((p3 ∨ p5) → ((p3 ∨ True) ∧ True))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98911376089479579003839151928 : ((True → (((((False → (True ∧ ((((p2 ∨ p4) → True) → False) ∨ p5))) → p5) → (((p2 → p4) ∨ False) → p1)) ∧ p5) ∧ (p4 ∨ p2))) → p5) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194778316847218047518177447034 : (((p5 ∨ ((p2 ∨ (p3 ∨ False)) ∧ p4)) ∨ True) ∧ ((False → (False ∧ ((((False → p2) → (p3 ∨ True)) → (p1 → p3)) ∨ p5))) → (True ∨ False))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136584170715599645622277495478 : (((p3 ∧ (p1 ∨ True)) ∨ ((((p4 → p3) ∨ (p4 ∨ ((p1 ∧ (True ∨ (False ∧ p1))) → True))) ∧ (p1 ∨ False)) → p5)) ∨ (p4 → (p3 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248139627015351134122828350684 : ((p2 ∨ False) ∨ ((p5 ∨ (p2 → ((((p3 ∧ p5) ∨ p5) ∨ p5) → (p3 → (p5 ∧ (False ∨ (((p4 → p1) ∨ (p1 → p5)) ∨ p5))))))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356531290375341735388366760119 : (p5 → (((False ∨ (False ∨ (False ∧ p5))) ∧ ((p4 ∨ p4) → p1)) ∨ ((p2 ∧ p5) ∨ ((((True → (False ∨ (p5 → p2))) ∧ p1) → p2) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243276250234785233076469818778 : ((p4 → p4) ∧ ((((p3 ∨ (p5 → ((p5 → ((p2 ∧ (p2 → p3)) ∧ True)) ∨ (((False → (False → True)) → p2) → p4)))) ∨ False) ∧ p2) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2094266794003918284606366239 : ((False ∧ ((p1 → ((p5 → (((p4 ∧ True) → (p1 ∧ p3)) → p4)) ∧ (p1 ∨ p4))) → p1)) ∨ (((True → False) → p2) → (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327232009815681822514850449575 : (True → ((p3 → (p3 ∧ ((p4 ∨ ((True ∨ p2) → ((p1 ∧ (p4 ∧ (((p4 ∨ (True ∨ p2)) ∨ p5) ∧ False))) ∧ p5))) ∨ (p2 → p3)))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637251779757705431845776099787 : ((((((((p4 ∧ p3) ∨ p3) ∨ (p1 → ((p3 → p4) ∧ p5))) → p1) → (p4 ∨ (((p3 → p3) ∧ (p4 → (True ∧ p4))) ∨ False))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665887029394388296721919334915 : ((((((((p4 → p3) ∨ (p2 ∨ (False → (False ∨ p4)))) ∨ p5) ∨ (p1 ∨ ((p4 ∨ (False ∧ False)) ∧ False))) → p3) ∧ (p5 ∨ (p2 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173239490853931124096213404434 : ((True → ((False → (True → ((p4 ∨ p3) → p4))) → (p1 ∨ (p3 ∨ (True ∧ p3))))) ∨ (p3 ∨ ((((p3 ∧ p1) ∧ p4) ∧ (p5 → True)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654570693361577813294575555825 : (((((p3 ∨ ((p5 ∨ (((True ∧ True) → (((p4 ∨ ((p1 ∨ p1) → p4)) ∨ p3) ∧ False)) ∨ (False ∨ True))) ∨ p1)) ∨ p1) ∨ (p1 ∧ p2)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591197911925299727316831074463 : (((((((p2 ∧ ((p5 ∧ (True ∨ (p4 ∧ p5))) → p3)) ∧ ((((p1 → p2) → False) ∨ p2) ∧ (True ∧ p1))) → p3) ∧ (p5 → p2)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199508233814300687887705265547 : (((p2 → (p4 ∧ ((p1 ∧ True) ∨ False))) ∨ False) → (((((False → p1) → p2) ∨ (((p3 → p5) → (p4 ∨ (p2 → True))) → False)) ∨ p2) → p4)) := by
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
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h6 : (False → p1) := by
          -- Implications on the right can always be decomposed.
          intro h7
          -- False on the left can always be used.
          apply False.elim h7
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h8 := h4 h6
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h9 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h8
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h10 := h5 h9
        -- We need to get the left conjuct of h10 based on <expert-advice>.
        let h11 := h10.left
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h14 =>
        -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
        have h15 : ((p3 → p5) → (p4 ∨ (p2 → True))) := by
          -- Implications on the right can always be decomposed.
          intro h16
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h17
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h13, we can now drive its conclusion.
        let h18 := h13 h15
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- False on the left can always be used.
        apply False.elim h19
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h21 =>
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h22 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h20
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h23 := h21 h22
      -- We need to get the left conjuct of h23 based on <expert-advice>.
      let h24 := h23.left
      -- One of the premise coincides with the conclusion.
      exact h24
    case inr h25 =>
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319470520375165099827252134720 : (p4 ∨ ((p4 ∨ ((p1 ∧ (((p3 ∧ p2) ∨ (p1 ∧ p3)) → p4)) ∧ False)) ∨ ((False ∧ (False ∨ ((p3 ∨ False) ∧ p1))) → ((p3 → False) ∨ True)))) := by
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
theorem thm_5_vars_197284363476510510129178979443 : ((((p5 ∨ (p4 ∨ p4)) ∨ (p5 → p4)) → p1) ∨ (p4 ∨ ((p1 → False) ∨ ((p2 ∧ p2) ∨ ((p2 ∨ p4) ∨ ((p5 ∨ p1) ∨ (p3 → True))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801929481329054565842879900677 : (((p2 → ((p5 ∧ p1) ∨ ((((p5 ∨ p1) → p4) → p4) ∨ ((p5 ∧ ((p5 → ((p1 ∧ (p2 → p1)) ∨ (p4 ∨ p3))) ∨ p1)) ∨ True)))) ∨ p2) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241517513820872112144840998157 : ((False → p3) ∧ ((((p5 ∧ (p2 ∧ (p5 ∧ (((p1 → p2) ∧ True) ∧ (p2 → p1))))) ∨ p1) ∨ ((p3 → p4) ∧ (p1 → (p1 → False)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245285148867013149878365265669 : ((p2 ∧ p2) ∨ ((p3 ∨ (((p5 ∨ (False ∧ p3)) ∨ (p3 ∨ (p1 ∧ p4))) ∨ ((False ∨ (p2 → (True → p4))) ∨ ((p4 ∨ True) ∨ p1)))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165195066466858947010507101211 : ((((True → (((False ∨ p3) ∨ p3) ∧ (((True ∧ p3) ∧ False) → p4))) ∧ p5) ∨ (True ∧ p4)) ∨ ((True → p4) → (((p3 → p5) ∨ True) ∨ p5))) := by
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



