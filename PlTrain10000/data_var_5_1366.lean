variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116317617204468225404435927583 : (((p5 → (p2 → p1)) ∨ ((p5 ∧ False) ∨ (p3 ∧ (((p2 ∧ p5) ∧ p5) ∧ ((True ∧ ((True ∧ (p2 ∧ True)) ∨ p5)) ∧ p3))))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758999966139984258164402194890 : (((p2 ∧ (((p5 → p2) → (p1 → (((p4 ∨ (p3 ∨ (True ∨ p2))) ∨ (False ∨ (p2 ∧ p2))) ∧ (p4 ∧ (p2 → (p5 ∧ False)))))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187795146532734383869320557946 : ((p3 → (p1 ∧ (True → (False ∧ (((p2 ∨ True) ∨ True) ∧ False))))) → ((p4 → ((True ∧ (p5 → p2)) → (False ∧ ((p2 ∧ p5) ∧ p1)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753816606678391700298961855049 : (((False ∧ ((((p2 → True) ∧ ((False ∨ p4) ∧ True)) → (p2 → False)) ∨ ((p1 ∨ p3) ∧ ((p4 ∧ ((p5 ∧ p3) → p3)) ∨ (p1 ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216663289629401527317539822807 : ((((p4 ∨ p4) ∨ False) ∧ True) → ((p2 ∨ (((((True → False) ∨ p1) ∨ ((p4 ∧ p1) → p4)) ∧ p2) ∧ p1)) ∨ (p1 → (p5 ∨ (True ∨ True))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9934486498952402491260015524 : (((p2 ∧ ((p3 ∨ (p1 → (((True ∨ ((p5 ∧ (True ∨ p2)) ∨ p5)) ∧ (False ∧ ((p3 ∧ (p5 → True)) ∨ p3))) ∨ False))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152548050053428252264326147464 : ((((p2 ∧ True) → True) → ((p3 ∨ (False ∨ (((p2 ∧ False) → (p3 ∧ p1)) ∧ (p2 → (p3 → p4))))) ∧ p1)) → (((p3 ∨ p4) ∨ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346582318825353558061998119026 : (p3 → (((((((p3 ∧ ((True ∨ p4) → (p1 → p1))) ∨ ((p5 ∧ p4) ∧ p3)) ∧ (p3 ∨ True)) → False) ∧ p4) ∧ p2) ∨ ((False → True) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314809523504085144462206062951 : (p3 ∨ (((p4 → (True → False)) ∨ (False ∨ (((p1 ∧ False) ∨ True) → True))) ∧ (((p5 ∧ (p5 ∨ p4)) ∧ ((True ∨ True) → p2)) → (p1 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160955669731288775818455136212 : ((((p1 ∧ False) → True) ∧ ((((p2 ∨ ((True ∧ (p4 ∨ (True ∨ p4))) → p2)) ∧ False) ∨ p3) ∨ p5)) → (p4 ∨ (((True ∧ p3) ∧ False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
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
        -- False on the left can always be used.
        apply False.elim h7
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h7
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356626923755134818175465421276 : (p5 → (((p2 ∨ (False ∧ False)) ∨ ((False → p5) → p2)) ∨ (True ∧ (((True ∧ True) → (((p3 ∨ True) ∧ p4) ∨ p5)) → ((p1 → True) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157718343329803418876453096469 : (((((p3 ∧ p3) → p3) ∨ ((p4 → ((p5 → p5) ∧ p4)) ∨ (p3 ∧ p2))) → (p3 ∧ (p1 ∧ p4))) ∨ (((False → p4) → p1) → (p1 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p4) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674934154709784257468973541868 : ((((((((True ∧ p1) ∧ p2) ∨ ((False → False) ∨ (p5 ∨ ((p1 ∨ p4) ∧ p5)))) → (p5 ∧ p3)) ∧ p4) ∧ (((p2 ∨ False) ∨ p2) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248583308826203913299024323854 : ((p3 ∨ False) ∨ ((((p2 ∧ (p2 ∧ p2)) → p3) ∨ ((p2 ∧ (True → p3)) ∨ True)) ∧ (((p3 ∧ (p3 ∨ p1)) ∧ (False ∧ p2)) → (p4 ∧ p5)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- False on the left can always be used.
    apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h13.left
    let h18 := h13.right
    -- False on the left can always be used.
    apply False.elim h17
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h13.left
    let h21 := h13.right
    -- False on the left can always be used.
    apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60393676106153724072541891473 : (((p3 → p4) → ((True ∨ p3) ∧ (((True ∨ p2) → (((p4 ∨ ((p5 → p3) ∧ p1)) → (((p2 → p1) ∧ p1) → p4)) ∧ p4)) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595803450166944593662727454144 : (((((False ∧ ((p5 ∨ ((p5 → True) ∨ p2)) ∨ (p5 ∨ p4))) ∧ ((((((True ∨ (p4 ∧ p2)) → False) ∨ p2) ∧ p4) → p2) → p2)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47264366417180925864539563863 : ((((False → (((p2 ∨ p5) → p4) ∨ p3)) → (((p1 ∨ p3) → ((p2 ∧ False) ∨ p4)) ∨ ((p3 → p2) ∧ (p1 → p5)))) ∨ (True ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41261097235293295029177677039 : (((((False → (p2 ∨ p1)) → ((True → (p3 ∨ (((p3 ∨ p2) → p2) ∨ p4))) → (p5 ∨ p2))) ∨ ((p3 ∧ p4) ∧ (p4 ∨ False))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117574106838766673147973128719 : ((p2 ∧ ((p4 ∧ p4) ∧ (((((p4 → (p5 → p3)) ∨ p1) ∧ p3) ∨ p4) ∨ (((False → (p3 → (p5 ∨ p2))) → p2) ∨ True)))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174305237705803283398244282395 : (((((p4 ∨ (p4 → (True ∨ p5))) → False) ∧ (p2 ∨ p5)) ∨ (False ∧ (True ∧ True))) → (p5 ∧ (p2 → (False ∧ (p1 ∧ ((True → False) → p2)))))) := by
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
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h6 : (p4 ∨ (p4 → (True ∨ p5))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h8 := h3 h6
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  -- Implications on the right can always be decomposed.
  intro h13
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h18 : (p4 ∨ (p4 → (True ∨ p5))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h20 := h15 h18
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h22 : (p4 ∨ (p4 → (True ∨ p5))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h23
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h24 := h15 h22
      -- False on the left can always be used.
      apply False.elim h24
  case inr h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- False on the left can always be used.
    apply False.elim h26
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h28 =>
    -- Conjunctions on the left can always be decomposed.
    let h29 := h28.left
    let h30 := h28.right
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h31 =>
      -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
      have h32 : (p4 ∨ (p4 → (True ∨ p5))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h33
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h29, we can now drive its conclusion.
      let h34 := h29 h32
      -- False on the left can always be used.
      apply False.elim h34
    case inr h35 =>
      -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
      have h36 : (p4 ∨ (p4 → (True ∨ p5))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h37
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h29, we can now drive its conclusion.
      let h38 := h29 h36
      -- False on the left can always be used.
      apply False.elim h38
  case inr h39 =>
    -- Conjunctions on the left can always be decomposed.
    let h40 := h39.left
    let h41 := h39.right
    -- False on the left can always be used.
    apply False.elim h40
  -- Implications on the right can always be decomposed.
  intro h42
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h43 =>
    -- Conjunctions on the left can always be decomposed.
    let h44 := h43.left
    let h45 := h43.right
    -- Disjunctions on the left can always be decomposed.
    cases h45
    case inl h46 =>
      -- One of the premise coincides with the conclusion.
      exact h46
    case inr h47 =>
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h48 =>
    -- Conjunctions on the left can always be decomposed.
    let h49 := h48.left
    let h50 := h48.right
    -- False on the left can always be used.
    apply False.elim h49



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161939247082636516965452935955 : ((p2 → ((True ∨ (((p4 → (p5 → p1)) → ((p1 ∧ p2) ∨ False)) ∧ ((False ∧ p5) ∧ p1))) ∧ p4)) → (((p2 → (False ∨ p1)) → p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326875804858320635185147305419 : (True → (((((p1 ∨ True) ∧ ((((p4 ∨ p2) ∧ (p1 ∨ (False → True))) ∨ (p3 ∧ p4)) → True)) → ((p1 ∧ (p3 → p3)) ∧ p2)) ∨ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165714203275743444316351652491 : ((((False → p1) ∧ (p5 ∨ p3)) ∧ (False → (p4 → ((p5 ∧ (p5 ∧ True)) ∨ (p4 ∧ False))))) ∨ ((p5 ∧ (True ∧ (False ∧ (p2 ∧ True)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193154228185528950151890700336 : (((p2 ∨ (p2 ∧ (p2 ∨ False))) ∨ (True ∧ (False ∨ p5))) → ((p1 ∧ (p4 ∨ p5)) ∨ (((p1 ∧ (p4 → False)) → (p1 ∨ p4)) ∨ (p1 ∧ False)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h20
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50056688496665636210067480012 : ((((p4 → p4) ∧ (((p3 ∨ (((p4 → False) ∧ p3) ∧ p2)) ∨ (((p2 ∧ p3) ∧ p2) ∨ p1)) ∧ p5)) ∧ ((True ∨ p5) → (False ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147276644016243729396896230117 : (((((((p4 ∧ False) ∧ p3) → False) → (False ∨ (((p3 ∨ p4) → ((p5 ∧ p2) ∧ False)) → False))) ∨ True) ∨ p2) ∨ (p1 → ((p3 ∧ p4) ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111906091443069415511562426800 : (((((((p3 → (p3 ∧ ((p5 ∨ p1) ∧ p4))) ∨ p3) ∨ p2) ∧ False) ∧ ((True ∧ (True → True)) → (True → (p1 ∨ p5)))) ∨ True) ∨ (True ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134612596194808770660349611624 : ((((((((p4 ∨ p3) ∧ ((p4 ∨ True) ∨ (True ∨ (p1 → True)))) → p2) ∧ False) → p3) ∨ (p5 → (True → True))) → p1) ∨ ((True → p5) → p5)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190136842332269316442150202045 : ((((False → p4) ∧ (((p2 ∨ True) ∧ p4) → False)) ∧ False) ∨ ((p3 ∨ p2) ∨ (((((True → True) → False) ∨ (p1 ∧ p2)) ∨ (p1 → True)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37054138658843369534896817686 : (((((((p5 ∨ ((p2 → (((p5 ∨ ((p4 ∧ p4) ∧ p3)) → p1) ∧ False)) ∧ p3)) → (False ∨ p4)) ∨ (p5 ∧ p4)) ∧ p3) ∧ p5) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748516626256975368937520854688 : ((((p3 → True) → ((p2 → (p4 ∨ (((p4 ∨ p3) → (False ∧ False)) ∧ p2))) ∨ (True ∨ ((p4 → (True → (False → (p2 ∧ p1)))) ∧ p1)))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175218741467220282710208061606 : ((p1 ∨ (((p1 → p1) ∨ (p2 → (((p5 ∧ False) ∧ (True ∧ p5)) → p3))) ∧ p3)) → ((p5 ∨ ((p2 → p3) ∧ (p5 ∨ p5))) → (p4 ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
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
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Disjunctions on the left can always be decomposed.
        cases h16
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
      cases h1
      case inl h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228840429267245987380911542307 : ((p3 ∨ (p1 → False)) ∨ ((p1 ∨ (p3 → (False ∨ (False ∨ ((p4 ∧ (False → (p1 → False))) ∧ ((p3 ∧ (p3 → p5)) ∨ p1)))))) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792334070072125124561040175481 : (((True → (((p5 ∧ p1) → (False → (((False ∨ ((p2 ∧ True) → (False ∨ p3))) → p3) → p1))) → (p2 ∨ (p2 ∧ (p1 ∨ (p2 → p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115923025903695524023038034453 : ((((p3 ∨ p5) → (p4 → False)) ∨ (((((p4 ∨ (p1 ∧ (True → (False ∨ ((p2 ∨ True) → p1))))) ∧ p3) → p4) ∧ p4) ∨ p2)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138482544033766449803098874835 : (((((((((p4 → p5) → (p2 ∨ False)) → True) → p4) ∧ ((p1 ∨ (p5 → p5)) ∨ p5)) ∧ (p5 → True)) ∧ p1) ∧ p2) → (p4 ∨ (p1 → p3))) := by
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
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h12 : (((p4 → p5) → (p2 ∨ False)) → True) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h14 := h8 h12
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h16 : (((p4 → p5) → (p2 ∨ False)) → True) := by
        -- Implications on the right can always be decomposed.
        intro h17
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h18 := h8 h16
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h19 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h20 : (((p4 → p5) → (p2 ∨ False)) → True) := by
      -- Implications on the right can always be decomposed.
      intro h21
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h22 := h8 h20
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234778519030839792568420734159 : ((p5 → (False ∧ False)) → ((p3 ∧ (((p1 ∨ (p2 → p4)) ∨ ((((p3 → p1) → p2) ∧ False) → p3)) → p3)) ∨ (p5 → ((p5 ∨ False) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151953972498591233761908225107 : (((((((p5 ∨ p4) → p1) ∨ False) ∧ (False ∨ (p3 ∨ p4))) ∨ p3) ∨ (p3 ∧ (((True ∧ p4) ∧ p3) → p3))) → (((True → p5) ∧ p4) → p5)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h10 =>
          -- False on the left can always be used.
          apply False.elim h10
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h13 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h14 := h3 h13
            -- One of the premise coincides with the conclusion.
            exact h14
          case inr h15 =>
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h16 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h17 := h3 h16
            -- One of the premise coincides with the conclusion.
            exact h17
      case inr h18 =>
        -- False on the left can always be used.
        apply False.elim h18
    case inr h19 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h20 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h21 := h3 h20
      -- One of the premise coincides with the conclusion.
      exact h21
  case inr h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h25 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h26 := h3 h25
    -- One of the premise coincides with the conclusion.
    exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150038365238662111828378542401 : ((p5 ∨ (p1 ∨ (False ∧ (((((p2 ∧ False) → False) ∧ False) → False) ∧ (((True → p3) ∧ (p4 → p5)) → False))))) ∨ (((p3 ∧ False) ∧ True) → p4)) := by
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
theorem thm_5_vars_58491261806468362740269206246 : (((p4 ∨ p2) ∧ ((True → ((p1 ∧ (((p3 → (True ∨ True)) ∧ ((False ∧ (p1 ∧ p1)) ∧ (p4 ∨ p4))) ∨ p5)) ∧ p3)) ∨ (p1 ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52976687780392063760931139253 : ((((p1 ∧ (p2 → (p2 → (p2 ∨ ((p4 ∧ p2) ∧ p4))))) → False) ∧ (((False ∧ True) ∨ ((((p2 ∨ p2) → p1) ∧ p1) → p4)) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7891403221631952934658380193 : ((((False ∨ (p5 ∨ (((False ∨ (p2 ∨ (((False ∧ (((p4 ∨ p2) ∧ True) → False)) ∧ (p4 → True)) ∧ p3))) ∨ p1) ∨ p1))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49032692410893846803049732803 : (((((False → True) ∨ (((p5 ∧ (p4 ∧ (True ∨ (False ∨ p4)))) → ((p2 ∧ p1) → p4)) ∨ (p4 ∧ False))) → p4) ∨ (p1 → (p5 → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767116492872782566459542200065 : (((p4 ∧ (p4 → ((((p4 ∧ ((p5 → p5) → (((True ∧ p3) ∧ p2) ∧ p4))) → False) → p2) ∧ ((True ∧ p5) ∨ (p4 → (False → True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700536587016412311709319084743 : ((((p5 ∨ (((False ∧ (p1 ∧ (p5 ∧ (True ∨ True)))) ∨ False) → p3)) → ((p5 ∨ (((p4 ∨ False) ∨ (p5 ∨ p1)) ∨ True)) ∧ (p2 ∨ True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321355820617208950311757713149 : (p4 ∨ (True → ((True ∧ ((p2 → (p2 → ((((p3 → p5) ∧ ((True → ((p3 → False) ∨ p4)) ∧ True)) → p3) ∨ (False ∧ p3)))) ∨ p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43622686017424520737659962901 : (((((p4 ∨ (((p1 ∨ (p4 ∨ p3)) ∧ (p3 ∨ ((p2 ∨ False) → (p5 → False)))) → (p4 ∧ (p4 ∨ (True ∧ p1))))) → p2) → p2) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656542340594592036577311734576 : ((((((((p1 → p4) → p3) ∧ p1) → (True ∧ False)) ∧ (True ∧ (((p3 ∧ True) ∨ p2) ∨ ((False ∧ p3) ∨ (p3 ∨ True))))) ∨ (p5 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351748051968405784414879720550 : (p4 → ((((p5 ∨ (((p2 ∧ (p3 → (p1 → p1))) ∧ True) ∨ p1)) → p1) ∧ p4) → ((p4 ∧ p2) ∨ (((p2 ∧ (True → p1)) → p5) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_480176151878728375953984177272 : (((((((True ∨ (p5 ∧ p1)) ∨ p3) ∧ p1) ∧ p1) ∨ ((True → (((False ∧ p5) ∨ ((p3 → p5) → p2)) ∨ (p1 ∨ (p4 ∨ True)))) ∨ False)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_582659173933599812243377226764 : (((p5 → (((p5 ∨ ((((p5 → (p5 → False)) → ((((p5 ∨ True) ∨ p3) → p3) ∧ False)) → ((True → p3) ∨ p4)) → p4)) → p4) ∨ True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_238253140737937954045854611144 : ((True ∨ p5) ∧ ((p3 ∧ ((p4 → ((((p1 ∨ p2) ∨ (p2 ∧ (p1 ∧ p1))) ∧ False) ∧ ((p2 ∧ p4) → p3))) → False)) ∨ ((p3 ∧ False) → p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_60349746689354359223652441897 : (((p2 → p3) → (False ∨ (p2 ∨ ((False ∧ ((p1 → ((p3 ∧ ((p3 → p5) ∨ p5)) ∧ p1)) ∨ p4)) ∨ ((p5 ∧ (p4 ∧ False)) → p5))))) ∨ p1) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192882664375275972095918380909 : (((p2 ∧ ((p2 ∨ True) ∧ (True ∧ p3))) ∧ (p2 → True)) → (((((((p3 ∨ (True ∧ p1)) → p3) ∨ p2) ∨ p2) ∧ (True → p1)) → p1) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h1.left
      let h8 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h12.left
        let h15 := h12.right
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h17 := h4 h16
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h12.left
        let h20 := h12.right
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h21 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h22 := h4 h21
        -- One of the premise coincides with the conclusion.
        exact h22
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h1.left
      let h25 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h24.left
      let h27 := h24.right
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h29.left
        let h32 := h29.right
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h33 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h34 := h4 h33
        -- One of the premise coincides with the conclusion.
        exact h34
      case inr h35 =>
        -- Conjunctions on the left can always be decomposed.
        let h36 := h29.left
        let h37 := h29.right
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h38 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h39 := h4 h38
        -- One of the premise coincides with the conclusion.
        exact h39
  case inr h40 =>
    -- Conjunctions on the left can always be decomposed.
    let h41 := h1.left
    let h42 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h43 := h41.left
    let h44 := h41.right
    -- Conjunctions on the left can always be decomposed.
    let h45 := h44.left
    let h46 := h44.right
    -- Disjunctions on the left can always be decomposed.
    cases h45
    case inl h47 =>
      -- Conjunctions on the left can always be decomposed.
      let h48 := h46.left
      let h49 := h46.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h50 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h51 := h4 h50
      -- One of the premise coincides with the conclusion.
      exact h51
    case inr h52 =>
      -- Conjunctions on the left can always be decomposed.
      let h53 := h46.left
      let h54 := h46.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h55 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h56 := h4 h55
      -- One of the premise coincides with the conclusion.
      exact h56
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341308386523095829757537258927 : (p2 → (((((p3 → ((((p1 ∨ p1) ∧ p4) ∧ p5) → (p3 ∧ p3))) → p2) → p5) ∧ ((((p5 ∨ p5) → p4) → False) ∨ (p5 ∨ p2))) → p5)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : ((p3 → ((((p1 ∨ p1) ∧ p4) ∧ p5) → (p3 ∧ p3))) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h6
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h12 : ((p3 → ((((p1 ∨ p1) ∧ p4) ∧ p5) → (p3 ∧ p3))) → p2) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h14 := h3 h12
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171799820929204707429633828221 : (((((((p5 ∧ (p2 → p5)) ∧ p3) ∨ p5) → p5) ∨ ((p4 ∨ p2) → p3)) → p3) ∨ (((p2 ∧ p4) → True) ∧ (p5 → (False ∨ (False → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742387657938039348949077168896 : ((((p1 → p4) ∨ (p4 ∧ ((False → (p2 ∨ p2)) → (False ∨ ((False ∨ (((((False ∨ p2) ∧ True) → p1) ∨ p3) ∧ (p3 ∧ False))) ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41024790940189692096798372777 : (((((((True ∧ (p4 → (((False → ((p4 ∨ p1) ∨ p2)) ∧ False) ∧ (p3 → p3)))) ∧ True) → p3) ∧ (p5 ∨ p2)) → (p4 ∧ False)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110880801847664955197702104597 : ((((((p3 ∨ ((True ∧ True) ∨ (p5 → (((p4 → True) ∨ p2) ∨ (p2 ∧ p4))))) ∨ p3) → (p1 ∨ (p4 ∧ p1))) → p2) ∧ p2) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219235137270892253904760507884 : ((p1 ∨ ((p4 ∨ p2) ∨ p4)) → (p1 ∨ (((p4 ∧ (True ∨ (((((True → p1) → p4) ∨ p5) ∨ True) ∧ p2))) ∧ (p3 ∨ p1)) ∨ (False → p1)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h6
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- False on the left can always be used.
        apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186941040869624845280190199104 : (((p3 → (p1 ∨ p5)) ∧ ((p1 → p1) ∨ ((p2 ∧ p4) ∨ p4))) → (((p5 ∧ ((False ∧ p3) → p5)) → ((p2 → False) ∧ p4)) ∨ (p2 → p2))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113614250865395632189734450011 : (((p5 ∨ ((((((p3 → p3) ∧ ((p3 ∨ ((p3 ∧ p3) → p4)) ∨ False)) ∨ p4) ∨ (p1 → p5)) ∨ p5) → p3)) ∨ (True ∨ p5)) ∨ (p4 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191903499408879045714572618114 : ((p5 ∨ ((False ∧ (p2 → p3)) ∧ (p2 → (False ∧ p2)))) ∨ (p2 ∨ (p5 ∨ ((True ∨ (p3 → (p5 → (True → True)))) ∨ ((False ∨ p5) → p1))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137637753983973033872385031700 : ((False ∨ ((p4 → ((False ∨ ((p2 ∨ False) ∧ p1)) ∨ ((p3 → (p3 ∨ p1)) → p5))) ∧ (p2 → ((p2 → False) ∨ p5)))) ∨ ((False ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158726176897379868070168445968 : ((p3 ∧ (((p1 → p2) ∨ p1) → (p2 → (p1 → ((p1 → (False ∨ p1)) → ((p2 ∧ False) ∧ True)))))) ∨ ((((p5 ∧ p5) ∧ p1) → p1) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166209686971836047246695697636 : ((p1 ∧ (p3 → ((((((p4 ∧ p2) ∧ p3) → True) → (p4 ∨ p5)) → (True ∧ p5)) ∧ False))) ∨ ((p4 ∧ p4) → (p2 ∨ ((p3 ∧ p1) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178199233991135077579634860595 : (((True ∨ (p5 ∧ ((((p3 → (p5 → p5)) ∧ p5) ∧ True) ∨ p4))) → False) ∨ (p1 ∨ ((p2 → p5) ∨ ((True ∨ ((p4 ∨ p2) ∨ False)) → True)))) := by
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
theorem thm_5_vars_165626302856319495167142662152 : (((((False ∨ p4) → (False ∧ p1)) → False) ∧ (p4 ∧ (p4 → (((p5 → p5) ∨ p1) ∧ True)))) ∨ ((p2 ∧ (p4 ∧ (p4 → (p1 → p5)))) → p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597654127423102268510951554294 : ((((((p1 ∨ (p1 ∧ p2)) → p5) → ((p5 ∨ (((((p5 → (False ∨ p3)) ∧ (True → (True ∨ p5))) → p3) ∧ p3) ∧ p3)) ∧ False)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111821663252952558342758157558 : (((((p3 → ((p4 ∨ (p3 → (p2 ∨ ((True ∨ p2) ∧ p4)))) → ((p1 ∨ p4) ∧ p2))) ∨ True) ∧ (p4 → (p4 ∧ True))) ∨ p1) ∨ (p3 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231818672664785271797870605285 : (((p4 ∧ p5) → p4) → (False ∨ (((((p5 ∨ (True ∧ (p1 ∨ ((p1 ∧ (p5 ∨ p4)) ∧ p4)))) ∧ p1) ∨ (p5 ∧ p4)) ∨ (False → True)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345651451112159955186174103616 : (p3 → ((p4 ∧ (p1 ∨ (((p2 ∧ ((p1 ∧ p5) ∧ (True ∧ (p4 → ((p2 ∧ p3) ∨ p3))))) ∧ (((False ∧ p4) → p2) ∧ True)) ∧ True))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41735346216491276350814921819 : ((((p1 ∧ (p2 ∧ (p2 ∨ p5))) ∧ ((((p2 → (p2 ∨ p1)) ∧ ((p1 ∧ ((p3 ∨ True) ∧ p4)) ∨ (p1 ∧ p2))) ∨ True) ∨ False)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114209915196075944232806984924 : ((((p4 → (p5 ∧ p3)) ∧ (((True → ((((p1 ∧ True) ∨ False) → (p5 → True)) ∧ True)) ∨ p2) → p1)) → (p4 ∨ (p1 ∧ False))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66215742863409791344948934488 : ((p5 ∨ ((p1 → (((p1 → (p5 ∧ p2)) → p5) ∧ (p2 ∧ (p1 ∧ True)))) ∨ ((p3 → ((p2 ∧ (False ∨ (p4 ∧ p2))) → p1)) ∨ True))) ∨ p4) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40323265288538051404139332233 : (((((((((False → p5) → (((False → p5) ∧ True) → False)) ∧ (p4 ∧ ((p1 ∨ False) → (p5 ∨ p2)))) ∨ p2) ∧ p5) ∨ True) ∨ p2) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624387540548591752545763514784 : ((((p3 ∨ ((p3 → True) → ((p2 → ((p4 → (p3 ∨ p4)) ∨ (False ∨ False))) ∧ (((p3 ∨ ((p2 ∨ p1) ∨ p5)) ∨ p1) → p1)))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_2211912140436737352951908895 : ((((p1 → p5) ∧ (p2 → (((p4 ∧ (p3 ∧ False)) ∧ (False ∨ p5)) → True))) ∨ p2) → (p4 ∨ ((p5 ∨ p5) ∨ (p3 → (False → p1))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
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
theorem thm_5_vars_178936404237175795960150700887 : (((False ∧ p2) ∨ ((((p1 ∧ p1) ∨ False) → ((p1 ∨ p4) ∨ p5)) → p1)) ∨ (True ∨ (((True ∧ ((p2 → (p5 ∧ False)) ∧ True)) ∧ p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788501953091501164846128874642 : (((p5 ∨ ((p4 ∧ (((p1 ∨ (p4 ∨ (((p1 ∨ (p3 ∧ ((False → False) → False))) ∨ p2) → p1))) ∧ p1) → (p3 ∧ (p1 → p1)))) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_119946177987186501305380881858 : ((((((p4 ∧ ((p2 ∧ (True → (((p4 ∧ (p4 ∧ p3)) ∨ p1) ∧ p2))) ∧ p4)) ∧ p2) ∨ True) → ((p4 → True) ∧ False)) ∧ p3) → (True ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p4 ∧ ((p2 ∧ (True → (((p4 ∧ (p4 ∧ p3)) ∨ p1) ∧ p2))) ∧ p4)) ∧ p2) ∨ True) := by
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
theorem thm_5_vars_231178841229089910904131141789 : (((p2 ∨ p4) ∨ True) → ((p1 ∧ ((p3 → (((p1 → True) ∧ ((p4 ∨ p2) ∧ ((p3 ∨ p1) → p5))) ∨ (p5 → p2))) → False)) ∨ (p2 → p2))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263420499491424639543512554235 : (True ∧ ((p5 ∧ (((p4 ∧ ((True ∨ ((p3 ∧ (p3 ∧ p1)) ∨ p5)) → p5)) ∨ p3) ∨ ((p4 ∨ p2) → (p2 → p4)))) ∨ (p3 ∨ (p5 ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740601984353769221630759283709 : ((((p2 ∨ p1) ∨ (((((p5 → (False ∧ (p3 ∨ True))) ∨ p2) → (False ∨ (p2 ∨ p5))) ∧ (True ∨ p1)) → ((p3 → p5) → (p5 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166513803915574504725322470123 : ((p4 ∨ ((((p4 ∨ (p5 ∨ (p3 ∨ True))) ∧ (False ∨ (p1 → p4))) ∨ p4) ∨ (False → p1))) ∨ (p1 ∧ (((False ∧ p3) → (p1 → p3)) ∨ p2))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308567701391612247903968115718 : (p2 ∨ ((((p2 ∧ p4) → (p1 ∧ (False → p2))) → (p5 → (p1 ∧ (((True ∧ p5) ∧ p2) ∧ (((p4 ∧ (p4 ∨ p2)) → p4) ∨ False))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347225939633524023574258546965 : (p3 → ((((((p3 ∧ p5) ∧ p5) → False) → False) → ((p4 ∨ p1) ∨ p4)) → (((p1 ∧ (p4 ∧ (p1 ∨ p5))) ∨ p2) ∨ (p3 ∨ (p3 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191165004174362091797675842896 : (((p4 ∧ (p2 ∨ False)) ∨ (p4 ∧ ((p1 → p3) → p1))) ∨ ((((p1 → False) ∨ ((True ∧ p2) → p1)) → (True → True)) ∨ ((False → False) → False))) := by
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
theorem thm_5_vars_322154628716797231006648401370 : (p5 ∨ ((p5 ∨ (((p3 → p2) → (False ∨ p3)) ∨ ((False ∨ (((p5 ∨ (p1 → (p2 ∧ p5))) ∧ (True ∧ True)) ∧ (p4 ∨ p2))) → True))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_13350806677361070449590060254 : (((True → (((p4 ∨ (False ∨ p3)) ∧ (p5 ∧ (p4 ∧ ((((False → False) → p4) → p2) ∧ (p3 ∨ p3))))) ∧ (False ∧ (p5 → p1)))) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191064323806903637570813385861 : (((False ∨ (p1 → (p4 → p1))) → (False ∧ (p3 ∨ p1))) ∨ (False ∨ ((p3 → ((p4 ∨ (p4 ∧ p1)) → True)) ∨ (p5 ∧ (True ∧ (True ∨ p3)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263793469051910733589509980166 : (True ∧ (((p3 ∨ (p2 ∧ ((p5 ∧ p4) ∨ (p1 ∨ ((False → (p5 → p4)) → p4))))) → False) ∨ ((((p2 ∧ (p4 → False)) ∨ p4) → False) → True))) := by
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
theorem thm_5_vars_44150889534808148034771151610 : (((((p4 → (((True ∨ p2) ∧ (p1 ∧ ((False ∧ ((True → p5) ∧ (True ∨ False))) ∨ p5))) ∨ p2)) ∨ p3) → (p5 ∧ (p5 ∨ p3))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64020927095355857196743002631 : ((False ∨ ((p5 → ((p4 ∨ p4) ∧ (False ∨ ((p4 ∧ ((p5 ∧ (p5 → p4)) → (p5 ∨ (False → False)))) → (p2 ∧ False))))) ∨ (p4 → p4))) ∨ p3) := by
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
theorem thm_5_vars_792219910055928182424131691673 : (((True → (((p4 → (p1 → (p4 ∨ (p4 ∧ p1)))) ∧ (False ∨ (p5 ∨ (((p3 ∧ p3) → p3) ∧ p2)))) ∨ (p5 ∨ (p5 ∨ (False → False))))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180982128770518523343288515416 : (((True ∧ p4) ∨ ((True → (p1 ∧ False)) ∧ (True → ((p3 → p5) ∨ p2)))) → ((((p2 ∧ True) → p3) → (False ∧ ((p5 → False) ∨ True))) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113350619932596730997496185821 : (((p1 ∧ (p3 ∨ ((((p2 ∧ p4) → False) → ((p2 ∨ p1) ∧ (p2 → p3))) ∨ ((p3 ∧ p2) → (p3 → p1))))) ∧ (False ∧ False)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40103203191761795344114926189 : (((((((p2 ∧ p5) ∨ p2) ∨ ((((p4 ∧ (p2 ∨ (p3 → p4))) ∨ p3) ∧ True) ∨ (p5 ∧ (p5 ∨ p4)))) ∧ (False ∨ p3)) ∧ p3) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32934635953177169497305242545 : ((p3 ∨ ((p3 → (False ∧ (((p3 ∨ p1) → (p1 ∨ (p2 ∧ (p2 ∨ p2)))) → (p4 ∧ ((p1 → p4) ∧ (p1 ∨ p2)))))) ∨ (p1 → p1))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126753360256303419351469760154 : ((p4 ∧ (p3 ∧ ((p1 → True) ∧ ((p2 ∨ (p4 ∧ (p5 ∨ ((p4 ∨ p4) ∨ (p1 ∨ p3))))) ∧ (p2 → (p3 → (p3 ∨ p4))))))) → (p5 ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h21



