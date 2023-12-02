variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61594306942647227349776965622 : ((p1 ∧ (((p2 ∨ p3) → p2) ∨ (p1 → (((p2 ∨ ((p4 ∨ p2) → p4)) ∧ (p3 → (False → (p2 → ((p2 → p5) ∨ p5))))) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303960284640198379111163633451 : (p1 ∨ ((((p2 → False) ∧ p4) ∧ (((True ∨ (p2 ∧ (p5 → p4))) ∨ (True → (((p3 ∧ (p1 → p5)) ∧ p4) → p5))) → (p3 ∨ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197033440600232822667109113572 : ((((True ∨ (False → p1)) → (False ∧ p2)) ∨ p5) ∨ ((p4 ∨ ((p5 ∧ p2) ∧ p4)) → ((True → p4) ∨ ((True ∨ (p1 ∨ (True → False))) ∧ p3)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159195169517891496214833875825 : ((p2 → (((p1 → p3) ∨ ((True ∨ (p3 ∧ p5)) ∧ ((p4 ∨ (p1 ∨ (False ∧ False))) ∧ True))) ∨ p4)) ∨ ((p2 ∧ True) ∨ ((False ∧ p3) → p4))) := by
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
theorem thm_5_vars_611531963843125535010332441434 : (((((p5 ∧ ((p5 ∨ (p1 → True)) → (p2 ∧ ((True ∧ p4) ∨ (p2 ∧ (p2 ∧ (p3 ∨ ((p5 → (True → p4)) ∧ p2)))))))) → p3) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111423290243182499722112471771 : (((p4 ∨ ((((p1 → ((p4 ∧ p4) ∨ (False ∨ (((False ∨ p3) → (p4 ∨ False)) ∧ False)))) → (p2 ∧ p4)) ∧ p2) ∧ p3)) ∧ p4) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228072990966125171871910992707 : ((p4 ∧ (p4 ∧ p3)) ∨ (p4 → (((((p1 ∧ (p3 → False)) ∨ (False ∧ (p2 ∧ (((p2 → p5) → p5) → False)))) ∧ p4) ∨ (p4 ∨ p1)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314539147920038799046629856190 : (p3 ∨ ((((((((False ∨ ((p4 ∨ p1) ∨ True)) → p3) → False) ∧ p3) ∨ p4) → (False → False)) → p1) ∨ (((p3 ∧ p5) ∧ p3) → (True ∨ p2)))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715169265968074424707363068024 : ((((True → ((False ∨ (False ∨ p2)) → False)) → (((((False ∨ p3) → False) ∨ False) → p2) ∨ ((((p3 → True) ∨ p2) ∨ (p2 → False)) ∨ p5))) ∨ p1) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66383280646941754999846001419 : ((p5 ∨ (p4 ∨ ((True → (((p1 ∨ False) → False) ∨ (p3 ∨ (p2 → (p1 → (p3 ∨ (True ∧ p1))))))) ∨ (p5 → (False → (p2 ∧ False)))))) ∨ p4) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114423781900190913106352503892 : (((False ∧ ((p2 ∧ (((True → ((True ∧ (True → (p1 ∧ p2))) → p3)) ∨ p4) ∧ False)) ∨ p5)) ∨ (p2 ∨ ((p5 → p2) → True))) ∨ (p3 → False)) := by
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
theorem thm_5_vars_168447796231925617821302557739 : (((True → p2) → (True ∧ (p4 ∧ (((p5 ∨ p5) → (False ∧ ((p2 → p5) ∧ p2))) ∨ p3)))) → (((p2 ∧ p1) → p3) ∨ ((p4 ∨ False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811662500929411597936071585305 : (((p5 → (p2 → ((((False → p4) ∧ ((True ∨ p4) ∨ False)) → (True → (p2 ∧ ((((True ∨ False) ∨ p3) → False) ∧ (False ∧ p1))))) ∨ True))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326955654991451417115352467108 : (True → ((((p1 ∨ p2) ∧ ((((p5 ∧ True) ∧ (p5 ∨ ((False ∧ p2) ∧ True))) ∨ ((p2 → (p4 → True)) → p4)) → p4)) ∨ (p1 ∨ True)) ∨ p4)) := by
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
theorem thm_5_vars_53302364587770437080877832407 : (((p4 ∨ ((((p3 → (True → (p2 → False))) ∧ p4) → False) ∨ p4)) ∨ (((p2 ∧ (p1 ∨ (((p4 ∧ True) ∧ True) → p3))) ∧ p3) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157414428072802555414813294815 : ((((p1 ∧ (((True ∧ p4) → p1) ∧ p1)) ∨ (((p4 ∨ p2) ∨ (False ∨ False)) → p4)) ∧ (False ∧ p5)) ∨ ((((p3 ∨ p2) → p1) ∧ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346924194328596141878799028531 : (p3 → ((p2 ∨ (p4 → ((False → (p3 → (p1 → (False ∧ (False ∧ (p2 ∧ p3)))))) → (p4 → p2)))) ∨ ((False ∧ p1) → ((p5 → p1) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134463120877326433157026300837 : (((((p2 ∨ (p4 ∨ p4)) → (((True → p2) ∧ ((((p4 ∨ False) ∨ True) ∨ p5) ∧ p3)) ∧ (p1 ∧ p5))) ∧ p3) → p5) ∨ ((p4 ∧ False) → p2)) := by
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
theorem thm_5_vars_178058010936822494174107630394 : (((((((p3 → p2) ∨ ((p5 → p3) ∨ False)) → p5) ∨ p4) ∨ False) → p2) ∨ ((True ∨ ((((True → False) → p1) ∨ p5) ∨ p4)) → (p5 ∨ True))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174266226627146385300340041657 : ((((((p4 → (False ∨ p2)) → p1) ∨ p1) ∧ (p3 → p2)) ∧ ((p3 → p3) ∧ p4)) → (p1 → ((p4 ∧ p5) ∨ (((p2 ∨ p2) → p4) → p1)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h4.left
    let h9 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h4.left
    let h13 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111345073204200230711249120201 : (((p3 ∧ (True → ((((True ∧ (p3 ∧ (p2 ∨ p5))) ∨ p2) ∨ (True ∨ (((False ∨ p4) ∨ p5) ∧ (False → p2)))) ∧ True))) ∧ p5) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116478899750128975227672845138 : (((p1 ∧ p4) ∧ (((p5 ∨ (((p2 ∨ ((p1 ∧ (p3 ∧ p4)) ∧ (p5 → False))) → ((True → p2) ∧ p5)) ∨ p1)) ∧ False) ∧ p1)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353685513506937421726630684932 : (p4 → (p5 ∨ ((p3 ∧ (True ∧ p4)) → (((True ∧ p2) ∨ (p5 ∧ True)) → (True → ((((False ∨ False) ∨ True) ∧ (True ∧ p4)) ∧ (p3 ∨ p2))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h2.left
    let h9 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h2.left
    let h16 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h2.left
    let h23 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- One of the premise coincides with the conclusion.
    exact h25
  case inr h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h26.left
    let h28 := h26.right
    -- Conjunctions on the left can always be decomposed.
    let h29 := h2.left
    let h30 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h31 := h30.left
    let h32 := h30.right
    -- One of the premise coincides with the conclusion.
    exact h32
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h33 =>
    -- Conjunctions on the left can always be decomposed.
    let h34 := h33.left
    let h35 := h33.right
    -- Conjunctions on the left can always be decomposed.
    let h36 := h2.left
    let h37 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h38 := h37.left
    let h39 := h37.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h36
  case inr h40 =>
    -- Conjunctions on the left can always be decomposed.
    let h41 := h40.left
    let h42 := h40.right
    -- Conjunctions on the left can always be decomposed.
    let h43 := h2.left
    let h44 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h45 := h44.left
    let h46 := h44.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h43



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158480788103578550891763117251 : (((True ∧ p4) → ((p5 → ((False → (p1 ∧ p1)) → (p3 ∧ (True → True)))) ∧ ((p2 → p5) ∧ False))) ∨ ((p2 → ((False ∨ p2) ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343495068790021069410951814622 : (p2 → ((True ∧ p1) → ((p4 → (((True ∧ p2) ∨ ((False → True) → (p2 ∨ p3))) ∨ p2)) → (((p2 ∨ p4) → ((p2 ∧ False) ∧ p4)) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h7 : (p2 ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h7
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115302104502571204062157945862 : ((((((p4 ∧ p3) ∧ p1) ∨ ((p1 ∨ p3) ∨ True)) → p2) → ((p4 ∨ ((p5 ∨ p2) ∧ p2)) ∨ ((p1 ∨ p4) ∨ (True ∧ False)))) ∨ (p4 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 ∧ p3) ∧ p1) ∨ ((p1 ∨ p3) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (((p4 ∧ p3) ∧ p1) ∨ ((p1 ∨ p3) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186938333381940983642759524327 : (((False → (p4 → p1)) ∧ (((p2 ∧ p1) → False) ∧ (True → True))) → (((((p4 ∧ p5) ∧ p4) ∨ (p2 ∧ ((True ∨ p5) ∨ p5))) → p4) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193256211649009662752294582737 : (((True ∨ (p2 → p4)) ∧ (((p1 ∧ p2) ∧ p2) ∧ p4)) → ((p4 → (((False ∨ (True → ((True ∧ p3) ∨ p5))) → (False ∧ p1)) ∨ p4)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h3.left
    let h14 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h19
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215038928045000792768973655266 : (((p2 ∨ p5) → (True ∧ p3)) ∨ ((True → (False ∧ True)) → ((p3 → (p4 ∨ ((False ∨ True) ∧ (p1 ∨ ((p2 ∧ p5) → (p3 → p1)))))) ∨ p2))) := by
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
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178614824928598950034203921335 : (((p5 → ((p4 → p5) → (p1 ∨ p4))) ∨ (((p3 ∨ p5) ∨ p4) ∨ p4)) ∨ (p5 → (((p5 ∨ p2) ∧ (p3 ∧ (False ∧ False))) ∨ (p5 ∨ p5)))) := by
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
theorem thm_5_vars_351753260269127498202485407075 : (p4 → (((((p5 ∨ ((p3 ∧ (True ∨ p2)) ∨ (p2 ∧ p5))) → p5) ∧ p1) → p2) → (p4 ∧ ((p2 ∨ (p5 → p1)) ∨ ((p5 ∨ True) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61182371220770020084414256762 : ((False ∧ ((p5 ∧ p1) ∧ (((False → ((((False ∧ p4) ∧ p1) → (p1 ∨ p5)) ∧ True)) ∧ ((((True → False) ∨ p4) ∧ False) ∨ p5)) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39236003472973140590607366040 : (((False ∧ ((((p1 → ((p2 → (p3 ∨ ((p1 → False) ∨ p3))) ∧ p3)) ∨ (p4 → True)) ∨ ((p3 → (False ∨ True)) ∨ p4)) ∧ p4)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609234176965419774905307559416 : (((((((p3 ∨ p1) → p1) ∨ (p4 ∧ ((p1 ∨ ((False ∨ p4) → ((((p5 → (True ∨ p3)) ∨ p3) ∨ False) → p2))) → p3))) ∨ False) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_595857595531791995573565243486 : ((((((True ∧ (((p5 ∨ p5) → p1) ∨ (p4 ∧ p5))) ∧ p1) ∨ ((p3 ∨ (p4 ∨ p5)) ∨ (True → ((p1 ∧ (p4 → False)) ∨ p5)))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328293426681766234320608224619 : (True → (((p1 ∨ (((False ∧ p5) ∨ p1) ∨ p5)) ∧ ((p3 ∧ False) ∨ (p5 ∨ ((p2 → (p3 → True)) ∧ p2)))) ∨ (((False ∨ p1) → p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121839528256897641819532833165 : ((((p3 ∨ False) ∨ (True ∧ (((p1 → False) ∨ p5) ∨ ((((p1 ∧ (p1 ∨ p3)) → p1) ∨ (p5 → p3)) ∧ (False → False))))) → p1) → (p1 ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ False) ∨ (True ∧ (((p1 → False) ∨ p5) ∨ ((((p1 ∧ (p1 ∨ p3)) → p1) ∨ (p5 → p3)) ∧ (False → False))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778213713302078853157223018657 : (((p1 ∨ ((p1 ∨ p5) → (((p3 ∧ (True ∧ p4)) ∧ False) ∨ (p3 → (((False ∧ True) ∧ p4) ∨ ((p3 ∧ False) → (p2 → (p3 ∨ p4)))))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746898140286154573279800018138 : ((((p4 ∨ False) → ((p1 ∧ (((p3 → (p1 ∧ p4)) → (p3 ∨ (((p5 ∨ p5) ∨ (True ∧ p2)) → p5))) → p3)) ∨ (True ∨ (False ∨ p1)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42531405742427187168634688277 : (((p1 ∨ ((True ∧ ((((True → p3) ∨ p2) → (p3 → (((((True ∧ p2) → p3) ∧ (p5 → p4)) ∨ p2) → p2))) ∨ p1)) ∨ True)) ∨ False) ∨ p3) := by
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
theorem thm_5_vars_619762282241226532454355166 : ((((p5 → (p5 ∧ (p4 → (((p1 ∨ ((p5 → ((True ∧ True) ∧ p1)) ∧ p5)) → False) ∧ p2)))) → (p3 → p4)) ∨ (p2 → p2)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54084374585555624153520287898 : ((((p5 ∧ False) ∨ (p4 → ((p2 ∨ (True ∨ p1)) ∨ True))) → ((((p4 ∨ p5) ∧ (True ∧ (p1 ∧ (False ∧ (p2 ∨ p3))))) ∧ p3) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323399425707360403847915154847 : (p5 ∨ ((p5 → (((((p2 ∧ True) → ((True ∧ p1) → (p3 → ((p5 ∧ False) ∨ ((p2 ∨ True) → p4))))) ∧ p3) → False) ∨ p1)) → (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352635465490039832585236564928 : (p4 → ((p1 ∧ p2) ∨ (True → ((p5 ∨ (((p3 → False) ∧ (p2 → ((((p1 ∧ p4) → p5) → (p3 → (False ∧ True))) ∧ p2))) ∨ True)) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179885897219170207171524922283 : (((((p2 ∨ ((p5 ∨ (p3 ∧ p3)) ∨ p1)) → (False → p4)) ∧ p2) ∨ p2) → ((((False ∧ (p4 ∧ (True → True))) ∨ p2) ∧ (p1 ∨ p3)) ∨ p2)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261274808089573351314192656786 : ((p5 → True) → (((((False → False) → p4) → (p4 → (p2 → ((p2 → p2) → p5)))) → p5) ∨ ((p4 ∨ p1) → (((p3 ∨ p3) ∧ p5) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166516347480756708589758565868 : ((p4 ∨ (((((p4 ∧ False) → (p3 ∨ p4)) ∧ False) ∧ (p2 ∧ p4)) ∨ (p3 ∧ (p4 ∨ False)))) ∨ (p1 ∨ (((p5 ∧ p3) → p1) → (False → p3)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350334697216464760132245651681 : (p4 → ((p1 → ((((p1 ∨ (False ∨ False)) ∧ p3) ∨ p2) ∨ ((p5 ∧ p2) ∨ (p1 → ((((True ∧ (p5 ∨ True)) ∨ p3) ∨ p5) ∨ False))))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158079099786989126740671255429 : ((((p5 ∨ True) ∧ (p3 ∧ (p5 → p4))) → ((((p4 ∨ p3) → True) → ((False ∧ p5) ∧ p4)) ∨ p3)) ∨ (((p4 → (True ∧ False)) ∧ True) → p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39674130945776645833582128894 : (((p4 ∨ ((False ∨ (((p5 ∨ (p3 → (p4 → (p2 ∨ ((p1 ∨ p5) → (p5 → (True ∧ p1))))))) ∨ (True → p2)) ∨ p4)) ∨ False)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304680661640054347173447668103 : (p1 ∨ (((False ∧ (p3 → (p2 ∨ ((p5 → ((p3 ∨ (p4 → True)) → True)) ∧ ((p5 → (p5 → p4)) ∧ (p1 ∨ p3)))))) ∧ p4) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_395408846981709749551420689681 : ((((p1 ∧ (False ∨ ((((((False ∨ True) ∧ ((p5 ∨ False) ∨ p3)) ∧ ((p3 ∧ True) → p5)) ∧ ((p5 ∨ p4) ∨ p4)) ∧ p1) ∧ p3))) ∨ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44514575508925144165912137461 : (((((((p1 ∨ (p2 → p1)) ∧ p5) ∨ p2) → (p2 ∨ p1)) ∨ ((((((p3 → p4) ∨ (True ∧ True)) ∧ p1) → True) ∨ p5) ∧ p3)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185915986676181554542956233437 : (((((p2 → (p1 → p4)) ∧ p5) → (True ∧ (True ∧ p2))) ∧ True) → (((((True ∨ (p3 ∨ p2)) ∧ p4) → ((p4 → p3) → p4)) → False) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (((True ∨ (p3 ∨ p2)) ∧ p4) → ((p4 → p3) → p4)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h9
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h14 := h2 h5
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693891443102216020784417614564 : (((((p1 → (p3 → (p3 ∨ ((p4 → (p2 → p1)) → (p1 → p1))))) → p3) ∨ (False ∨ ((((False ∨ False) ∧ (True ∧ True)) ∧ False) → p3))) ∨ p3) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58880001516701605587796976821 : (((False ∧ p1) ∨ ((p2 ∨ ((p3 ∧ (False ∧ ((p2 ∧ p4) ∨ True))) → (False → (p4 → p3)))) → (((p1 → p1) ∧ False) ∧ (p5 ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148029267661986182865139599724 : (((((p5 ∨ True) ∧ p4) ∧ (((p3 ∧ True) ∨ (True → ((p4 ∧ p1) ∨ (True ∧ False)))) ∨ p3)) ∨ (p5 ∨ True)) ∨ (p5 ∧ ((p1 ∧ True) → p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259788684549598983397788827875 : ((p1 → p2) → (p5 → (((p1 ∨ True) ∧ True) ∧ ((((True ∧ (p5 ∧ p1)) ∨ p3) ∧ False) ∨ (((p1 ∧ (p5 ∧ p4)) ∧ (p3 → True)) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113084342829980667902457226951 : (((p4 ∨ ((p5 → True) → (((p2 ∨ ((p2 → (False ∨ (False ∨ p2))) ∨ (p5 ∧ (p5 ∨ (False → p2))))) ∧ p3) ∧ False))) → p5) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58604881963370462313736698724 : (((False → p1) ∧ (((((True → False) ∨ p4) ∨ p3) ∧ p3) ∧ ((p1 ∧ (((False → (p1 ∨ (True ∨ (False → True)))) → p3) → p4)) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341107956204250691448386974779 : (p2 → ((p4 → (p5 → ((p4 → (False ∨ ((p5 ∧ False) ∨ ((p3 ∨ ((p4 → (p1 ∧ True)) ∨ (p3 ∧ (p3 ∨ p2)))) ∨ True)))) ∧ True))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2105827986947689093165046738 : (((((((True ∨ True) ∨ (p2 ∨ True)) → p1) → (False ∧ p4)) ∧ ((True ∧ True) ∧ p3)) ∧ True) → ((p4 ∧ ((False → True) → p4)) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337654215757656672290579702824 : (p1 → ((((((p4 ∨ p3) ∧ (p5 ∧ p1)) → ((p3 → (False ∧ p2)) ∧ p5)) ∧ (p3 → p1)) → p4) ∨ (((p2 → p2) ∧ (False → False)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138342689683739616714204212958 : ((p4 → ((p3 ∨ ((p2 → ((((((p1 → p4) → p3) ∨ p5) ∧ p1) ∨ (p2 ∧ p3)) ∨ (p1 ∨ p3))) ∧ p4)) ∧ p5)) ∨ ((p2 ∨ False) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206428598367097296873065983763 : ((p4 ∨ (((p5 ∧ p5) ∧ p3) ∧ False)) ∨ (True ∨ (p1 → ((True → (p2 ∨ (p1 ∧ True))) ∨ (((p2 ∨ p2) ∧ (p3 ∨ p2)) ∧ (p3 ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184053536197316411069231033554 : ((((((p5 ∨ p1) → (p1 → p2)) ∨ p1) ∨ (p1 ∧ p1)) ∨ p4) ∨ ((p4 → p2) → (p4 ∨ (p3 → ((p2 → True) ∨ ((p4 ∨ True) → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37759051461189533621922831874 : (((((((p3 ∧ True) → True) → False) → ((p4 ∨ p1) → (p3 ∨ ((p4 ∨ True) → ((False ∧ (p1 → (p4 → True))) ∨ False))))) → p2) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780428782415900047437790189547 : (((p2 ∨ (((p3 ∨ (False → p4)) ∨ ((((p2 → (p1 ∨ p4)) → p2) ∧ (p4 ∨ p2)) → False)) → (p5 → (((p3 ∧ False) ∧ p4) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634983615745870403444934932556 : ((((((False ∧ ((p2 ∨ False) ∧ (((((p5 ∧ p1) ∨ ((False ∧ p4) → p3)) ∧ p3) ∧ p3) ∧ False))) ∧ True) → (p1 → (p2 ∧ p1))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233896627716675697958274892661 : ((p4 ∨ (p4 ∨ p1)) → ((p1 ∧ ((p1 → p5) ∧ p1)) → ((p2 ∧ (((p5 → p3) → (p2 ∧ p4)) → p2)) ∨ ((True ∧ (p1 ∨ False)) ∧ p5)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h12 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h13 := h5 h12
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h15 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h16 := h5 h15
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113544920627822909719144779208 : (((((p2 ∧ p1) → p5) ∧ (p1 → (p3 ∧ (p5 → (p2 ∧ (p3 ∧ (((False ∨ True) ∨ (p3 ∧ p3)) → p3))))))) ∨ (p1 ∨ True)) ∨ (p2 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342268945563070956304112724963 : (p2 → ((((((((True → (p2 ∨ True)) ∧ p4) ∨ (p4 ∨ p1)) ∧ (p2 ∧ p4)) ∧ True) ∧ True) ∧ p5) ∨ (p4 ∨ (((True ∧ False) ∧ p2) → False)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790116413744894163828964375067 : (((p5 ∨ ((p1 ∨ p4) → (p3 → ((((((True → ((False ∨ (p4 ∨ p2)) → p4)) → p2) → p2) ∧ (p1 ∧ (p3 ∨ p1))) → p3) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608509911320114625414667157524 : (((((((True → ((p4 → p5) → p2)) → (((p3 → (True → (p5 → (p3 → p4)))) → p4) ∨ (p5 ∨ (p2 → p2)))) → p1) ∨ p5) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_311946047034117614298308462618 : (p2 ∨ (p3 ∨ ((((p2 ∨ (p1 ∨ False)) ∨ ((((p1 ∧ p3) → p2) → p2) → p3)) ∧ True) ∨ (((True → ((p5 → p3) ∨ p2)) → True) ∨ p3)))) := by
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
theorem thm_5_vars_110986310436322362883566912530 : (((((False → p1) → ((((p3 ∨ ((p4 ∧ (p5 → ((p5 → False) ∧ p3))) ∨ p5)) → False) ∨ p3) ∧ p4)) → (p2 → False)) ∧ p1) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187507180053764587552893968548 : ((p1 ∨ (((p5 ∨ ((p5 → (p2 ∧ p2)) ∨ p2)) ∨ p2) ∨ p4)) → (((p2 ∧ True) → (True ∨ (p4 ∨ p4))) → ((p3 → p5) → (p1 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
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
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h11 =>
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774151878042057585616804718999 : (((False ∨ ((((False → ((False → p3) ∧ True)) ∨ True) ∨ ((p3 → (False → p1)) ∨ ((p5 ∨ p2) → (p2 → (False ∨ p5))))) → (p5 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727381796143292207927373568568 : ((((p2 ∧ (p4 ∨ p2)) ∨ (((True ∨ False) → ((((False → p2) ∨ p2) ∨ p4) → p4)) ∧ ((p1 → (p5 ∧ (p4 ∧ (p1 ∧ p2)))) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247789638585845959046661556123 : ((p1 ∨ p1) ∨ ((((True → (True ∧ (False → (p1 → (p1 ∨ p4))))) ∧ ((p2 ∨ p4) ∨ p3)) ∨ (False → p3)) ∨ ((False → p3) → (p4 ∧ False)))) := by
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
theorem thm_5_vars_48690921229806260251078627927 : (((((p1 → p2) ∧ (p1 ∧ ((p5 ∨ p3) ∨ True))) ∨ ((p3 ∨ (p3 ∨ (p5 ∧ ((p5 → p1) ∧ p4)))) → p4)) ∧ (True → (True ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191357550439093049419010573190 : (((p3 ∨ p4) ∨ (p2 → ((False → (False ∨ p1)) → p3))) ∨ ((False ∨ p3) → (True ∨ ((p3 → p3) ∨ (p3 → (((p5 ∧ p5) ∨ p4) ∨ p2)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323666209243388306197192982812 : (p5 ∨ ((((p4 ∨ (((p1 ∧ p5) ∨ False) ∨ (p4 ∨ False))) → (p1 ∧ False)) ∨ (False ∨ (p2 ∨ (True ∨ False)))) ∨ (p3 ∧ (p3 → (p1 ∧ False))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138454871455813180769205687230 : ((p5 → (p3 ∧ ((((p1 ∧ (p2 → p2)) → True) → (p2 → False)) ∨ ((p3 ∧ ((p1 → p3) ∧ (False ∧ p5))) ∧ p4)))) ∨ (True ∨ (p4 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68182214022659783381605975045 : ((p3 → (((p4 → (((((p1 ∧ p1) ∨ p2) ∨ ((((False ∨ p3) ∧ True) ∧ ((True ∧ p2) ∧ p2)) → p1)) ∨ p2) ∧ False)) → False) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39215579328235105962041647086 : (((True ∧ ((((((True ∧ p3) ∨ p1) → p3) ∨ p3) ∨ p1) ∨ ((p1 ∧ ((((p3 → False) → (p3 → p4)) ∨ p4) ∧ p3)) ∧ True))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217718269650442777134425565233 : (((False ∧ (p5 → p1)) → False) → ((False ∨ ((False ∨ ((p2 → p5) ∧ (((p3 → (p5 → p1)) ∧ p4) ∨ ((p4 ∨ p4) ∨ p1)))) ∧ True)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214840568805537829707582861069 : (((p5 ∨ p5) ∨ (True ∧ p5)) ∨ (True → ((p4 ∧ (((True → p1) ∨ ((True → p4) → p3)) ∨ (p3 ∧ True))) → (p3 → ((p1 ∧ p5) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115351931185221616825321489137 : ((((((p2 ∧ p4) ∨ p5) → (p3 → False)) ∧ p4) ∧ ((p3 ∨ (True ∧ p4)) → ((p5 ∨ p1) ∧ (p2 ∧ (p2 ∨ (p5 → p2)))))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322593866227475336960771976419 : (p5 ∨ ((p1 → ((p5 → (p5 ∧ ((p3 ∧ ((p1 → p2) → ((True → p4) ∨ (True ∧ p4)))) ∨ ((p5 ∨ (True ∨ p5)) ∧ True)))) ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184430274121707985929129124392 : ((((p5 → (p3 ∨ p2)) ∧ ((p5 → False) ∧ p3)) ∧ (p5 ∧ p2)) ∨ (p4 → ((p4 → (True ∧ p4)) → ((((p3 ∨ False) → True) ∨ p1) ∨ True)))) := by
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
theorem thm_5_vars_786251758266232777272386051916 : (((p4 ∨ ((p4 → (((p1 → (p1 ∧ p5)) → (p2 ∧ (False ∨ ((True ∨ False) → p4)))) ∨ (p4 → p5))) ∧ ((p3 ∧ p4) ∨ (p1 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301825778604592472097482152414 : (False ∨ ((p2 ∨ p1) ∨ ((((((p5 ∨ p2) ∧ p3) ∨ True) ∨ (p5 ∧ False)) ∧ (False ∧ p4)) ∨ ((False → False) → (True ∨ (p1 ∨ (False ∧ p1))))))) := by
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
theorem thm_5_vars_66567924597540478598663044291 : ((True → (((True ∧ p2) ∨ ((False ∨ ((p5 ∧ ((p4 ∧ (p5 → True)) ∧ (p5 ∨ (p5 → (p3 → p1))))) → p1)) → p4)) ∨ (True → True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_95477506067012824431888919748 : ((p5 ∧ (((p2 ∨ (((True ∧ p5) ∨ (((p5 ∧ ((p3 ∧ p4) ∧ ((p5 → p2) → p5))) ∧ p4) ∧ (p4 ∨ p2))) → p2)) ∨ True) → p4)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p2 ∨ (((True ∧ p5) ∨ (((p5 ∧ ((p3 ∧ p4) ∧ ((p5 → p2) → p5))) ∧ p4) ∧ (p4 ∨ p2))) → p2)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51924406291075409937515260341 : (((((p5 ∨ p5) ∨ (((p4 ∧ (p2 ∨ p3)) ∧ p4) ∨ p1)) ∧ (True ∧ (p1 → True))) ∨ (((p1 → ((False ∧ p4) ∧ p5)) ∧ p5) → p5)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_144573762273933524256989095832 : (((p1 ∧ (False ∨ (p2 ∨ ((False ∧ (p1 ∨ ((True ∨ ((p4 → False) → p4)) ∧ p2))) ∨ p1)))) ∨ (True ∨ p3)) ∧ ((p4 ∨ (True → p1)) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347328777640817822501632967455 : (p3 → ((True → ((((p4 → False) ∧ (p2 ∨ p3)) → p2) ∨ p4)) → ((((p5 ∨ p3) → p4) ∨ (True ∨ ((p4 ∧ p1) ∧ (p5 → p3)))) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
theorem thm_5_vars_50923506732528433697966067593 : (((((p5 ∧ False) ∧ (p1 → ((p4 ∨ p3) → (p2 → (p2 ∧ True))))) ∧ (True → (p3 ∨ p2))) ∧ ((p3 → ((False → False) ∨ p4)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178277234178795504935529662805 : ((((p4 → False) ∧ (p2 ∧ ((p3 ∧ (p2 ∨ False)) → p4))) ∧ (p3 ∧ p2)) ∨ ((p1 ∨ (p2 → (True ∨ (False ∨ (p5 ∧ (p1 → p3)))))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



