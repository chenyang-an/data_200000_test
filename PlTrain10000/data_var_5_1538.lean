variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327459968517588695705364549805 : (True → (((p3 → (p5 → ((p1 → (False ∧ (p2 → p5))) → p1))) ∧ (p1 ∧ (True → (True ∧ (p5 ∧ ((False ∨ (p2 ∧ p3)) ∨ False)))))) → p3)) := by
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214142300480233104946064702812 : ((((p4 → p2) ∨ p3) → p3) ∨ ((((((False ∨ p4) ∨ ((True ∨ p2) → (p4 ∧ p4))) ∧ p2) → p4) → (False ∨ False)) → (p3 ∨ (False ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((False ∨ p4) ∨ ((True ∨ p2) → (p4 ∧ p4))) ∧ p2) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h9 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : (True ∨ p2) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h11 := h9 h10
      -- We need to get the left conjuct of h11 based on <expert-advice>.
      let h12 := h11.left
      -- One of the premise coincides with the conclusion.
      exact h12
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h14 =>
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232726408789007322396899634510 : ((p1 ∧ (True → False)) → (False ∨ ((p5 → ((p1 ∨ p3) ∨ (((p4 ∨ ((p2 → p1) ∧ (p5 ∨ p4))) ∧ p2) ∧ p5))) → ((True ∨ True) → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231153121229912970842150179354 : (((p2 ∨ True) ∨ p2) → (((False ∧ ((p1 → False) → ((p2 → p1) ∨ (((True ∨ ((p5 → p3) ∧ p4)) → p1) → False)))) ∧ True) ∨ (p4 → p4))) := by
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
theorem thm_5_vars_314272594259549891136822970799 : (p3 ∨ ((p3 ∧ (False ∨ (((p1 → p2) ∧ ((p3 ∧ True) ∨ p2)) → (p3 → (((p4 → p2) ∧ p1) ∧ (p1 → p5)))))) ∨ (True → (False → p3)))) := by
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
theorem thm_5_vars_148837667355137081172445138209 : ((((False ∧ (p1 → p2)) ∨ p2) ∧ (p1 ∧ (p5 → ((True ∧ ((p3 ∨ (p4 → p4)) ∧ (p1 ∧ p2))) ∧ p4)))) ∨ (True ∧ ((False → p1) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178079818890480169813416360331 : ((((((p3 ∨ p4) → ((True → p2) ∧ (p4 ∨ False))) ∨ p4) → p5) → False) ∨ ((False ∧ False) → (True ∧ (True ∧ ((p5 ∧ (True → False)) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80301122690582936804052786175 : (((((((p3 ∨ (True ∧ p4)) → (((p5 → p5) ∨ p3) → True)) → (p1 ∧ p5)) ∨ (True ∨ p4)) ∨ ((True ∧ p4) → p4)) → (False ∧ False)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p3 ∨ (True ∧ p4)) → (((p5 → p5) ∨ p3) → True)) → (p1 ∧ p5)) ∨ (True ∨ p4)) ∨ ((True ∧ p4) → p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64572058104739534816371774429 : ((p1 ∨ ((p2 ∨ (True ∧ False)) ∨ (p3 ∧ (p5 → ((False ∨ False) ∧ ((((p1 → True) → ((p4 → True) → p4)) ∨ (p2 ∨ p5)) ∧ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52983684125748412902734102787 : (((((p1 ∧ (True ∧ (p5 → (p1 ∧ p5)))) ∨ p1) ∧ (p5 ∧ p3)) ∧ (((p2 → ((p1 ∨ True) ∧ ((p4 ∨ p3) ∧ p2))) ∧ p3) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611801879976967235509937005106 : (((((p2 → ((((True ∧ p3) ∧ (p3 ∧ (((p3 → p2) ∧ p5) ∧ ((p5 ∨ p5) ∧ True)))) ∧ (p3 → (True ∨ p1))) ∨ p3)) → p2) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590929186629224965439337809956 : (((((False → ((p1 ∨ ((((p4 ∨ False) ∧ False) ∧ (False → p5)) ∨ p3)) ∧ (p4 ∧ (False → ((True → (p4 ∨ False)) ∨ False))))) → p1) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253621628460225428830785795686 : ((p1 ∧ True) → (((p5 → False) → ((((p1 ∨ p1) → (((p1 → True) ∧ p2) ∧ True)) ∨ p3) ∧ p4)) ∨ (((p1 ∨ p4) → p1) → (False → p3)))) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254898162252129245461475168779 : ((p4 ∧ True) → (((p2 → ((True ∧ ((p1 → p5) → (p2 ∨ (p5 ∧ p5)))) → p1)) ∨ True) ∨ (((p5 → True) → (p4 ∧ p1)) → (p4 → p4)))) := by
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
theorem thm_5_vars_351268707061189002699849354455 : (p4 → ((p3 → (((False ∨ (p3 ∧ (((p3 ∨ p3) ∧ ((p2 ∧ p2) ∧ (p5 ∧ (False ∧ True)))) ∧ p5))) ∨ p2) ∧ p5)) ∨ (p2 ∨ (p4 → True)))) := by
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
theorem thm_5_vars_262254134864028422365204009916 : (True ∧ (((((((p4 ∨ (p1 → p5)) ∨ ((p1 → ((p1 ∧ p3) ∨ False)) ∨ p4)) ∨ (p1 ∧ p3)) ∧ p5) ∧ p5) ∨ ((True ∧ p1) ∨ p4)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173206728165541925903730975340 : ((p5 ∨ ((p3 ∧ (((p2 → p1) → (p5 ∧ True)) ∧ p1)) ∧ (True ∨ (p3 → True)))) ∨ (p5 ∨ (((False ∨ p4) ∨ (False ∧ p5)) ∨ (p4 → p4)))) := by
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
theorem thm_5_vars_82449566756661793530710074944 : (((p1 ∧ (True → (p2 ∧ ((p4 ∨ p4) ∨ (((p1 ∨ p4) ∨ (p1 ∨ (p2 ∨ (p4 → True)))) → p5))))) ∧ ((True → p3) ∨ (p3 → p4))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h12 := h5 h11
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67884559440185674697366521959 : ((p2 → ((p3 ∧ (True ∧ (p3 ∧ (((p4 → p5) → ((p5 → p1) ∧ ((True ∧ True) ∨ p2))) ∨ p3)))) ∨ (((p2 → p1) ∧ False) ∨ True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116160027272783996900541663440 : (((p4 ∨ (p3 ∧ p5)) ∧ ((p2 ∧ (p5 ∨ ((((True ∨ p2) ∨ ((p4 → (p2 ∨ p2)) → True)) → p5) → (p4 → p5)))) ∨ False)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81822109105224186436296134879 : ((((p4 ∨ (((p5 → (p1 ∨ ((False ∨ p1) ∧ ((False ∧ True) ∧ (False → p2))))) ∨ (p3 → True)) → p3)) ∨ True) → (False ∧ (p1 ∧ True))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∨ (((p5 → (p1 ∨ ((False ∨ p1) ∧ ((False ∧ True) ∧ (False → p2))))) ∨ (p3 → True)) → p3)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64089186777850483821879423950 : ((False ∨ (((p5 → (False ∨ p3)) → ((p4 → (p1 → (p3 ∧ p3))) ∧ p1)) ∨ ((True ∨ False) ∨ (True → (((p1 ∧ p2) ∨ p3) ∨ p2))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_248825376330904830229822924187 : ((p3 ∨ p4) ∨ ((((p1 ∨ p1) → True) → (((p3 ∨ p1) ∨ p4) ∧ (True ∧ (p5 ∨ p5)))) ∨ ((p3 ∨ (p4 → False)) ∨ (False → (p4 ∧ p4))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45301429996566991575201211856 : (((p2 ∧ (p1 → ((((p1 → (False ∨ ((False → p1) ∧ (p2 ∨ (p5 ∧ (p1 ∨ False)))))) ∧ p1) → (True → (p4 ∧ p5))) ∧ p2))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209278751597919623559585137108 : ((True → ((p2 ∧ (p3 ∨ p5)) ∨ True)) → (((False ∨ p3) → ((((p5 ∨ (True → (p2 → p1))) → p5) ∨ False) ∨ ((False ∧ p3) → False))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350211214861878967938068132452 : (p4 → (((p3 ∧ p5) ∧ (p4 → ((p4 → (p2 ∨ (True → ((False → p1) ∧ (p2 ∨ ((p1 → (p3 → p3)) ∨ p5)))))) → (p1 ∧ p1)))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46081531375471856839381458610 : ((((((p2 ∨ p1) ∧ ((p5 ∧ p1) ∨ ((p5 ∨ (p2 ∧ p2)) ∧ (p1 ∨ (p2 ∧ p5))))) → ((False ∨ p5) ∨ p4)) ∨ p1) ∧ (p4 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187659068932916742475205710050 : ((True → ((False ∨ ((p3 ∨ (p4 → (True → p5))) ∧ p4)) ∨ p2)) → (p2 ∨ ((((((p5 ∨ p5) ∨ p1) ∧ True) ∧ p3) → False) ∨ (True ∨ False)))) := by
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
theorem thm_5_vars_655876201916339642677274672305 : ((((((p4 → p3) → (p2 ∧ (((((False ∨ p1) ∧ p2) ∧ False) ∧ p2) → (p3 ∧ (p2 ∨ True))))) → ((True ∧ p2) ∧ p2)) ∨ (False → p2)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_638476564348853379308838330694 : (((((((p5 ∨ p3) ∧ (True ∨ p1)) ∨ False) ∨ ((p2 ∧ p4) ∧ (p5 ∨ ((p3 ∧ (p1 ∧ p2)) ∧ (True ∧ ((p3 ∧ p3) → True)))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168040854983754949351918830613 : ((((p4 ∧ (p2 ∧ p1)) → (p1 ∧ p2)) → ((p2 → (((p1 ∧ p3) ∨ p5) ∨ True)) → p5)) → ((p1 ∧ (p5 → ((p5 → p2) ∨ False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165584154419786418345183910074 : (((p5 ∧ ((p3 ∨ p1) ∨ (True ∨ (p2 ∨ p5)))) ∨ ((p4 ∧ False) ∨ ((p3 ∧ p2) → True))) ∨ (p5 ∨ (((p2 ∧ (p2 → p4)) → True) → p3))) := by
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
theorem thm_5_vars_172506060070799296952149754996 : ((((False ∧ p2) ∨ p3) ∧ ((((p2 ∨ (p5 ∧ p1)) ∧ (p3 → p3)) ∨ False) ∨ p5)) ∨ (((p5 ∨ True) ∧ ((False → p3) ∨ p5)) ∨ (p5 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213558192879918003301815945825 : ((((True ∨ p2) ∧ p3) ∨ p5) ∨ ((p3 → ((p2 ∧ ((p2 ∨ p1) → ((p5 → True) → True))) ∨ True)) ∧ (((p4 ∧ False) ∨ (p3 ∨ p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613541247134974551821131593673 : (((((((p2 → p5) ∨ ((p1 → ((p5 ∧ (p3 ∨ (((p5 → p3) ∨ p2) ∨ True))) ∨ p5)) ∧ p1)) ∧ False) ∧ ((p1 → p1) → False)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258109036539291568925900229017 : ((p4 ∨ p3) → (((p3 → (p5 → ((((False ∧ p2) → True) ∧ ((False ∧ (p1 → p3)) ∧ (p1 ∧ p3))) → (p1 ∨ True)))) → p1) → (False ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : (p3 → (p5 → ((((False ∧ p2) → True) ∧ ((False ∧ (p1 → p3)) ∧ (p1 ∧ p3))) → (p1 ∨ True)))) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- False on the left can always be used.
      apply False.elim h12
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h16 : (p3 → (p5 → ((((False ∧ p2) → True) ∧ ((False ∧ (p1 → p3)) ∧ (p1 ∧ p3))) → (p1 ∨ True)))) := by
      -- Implications on the right can always be decomposed.
      intro h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- Implications on the right can always be decomposed.
      intro h19
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h22.left
      let h25 := h22.right
      -- False on the left can always be used.
      apply False.elim h24
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h26 := h2 h16
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42889692228389339650581950645 : (((p3 → ((True ∨ (((False ∧ p5) ∨ (p1 → (p3 ∧ ((p1 ∧ ((p4 ∨ (p5 ∧ p1)) → True)) ∨ p4)))) → (p3 ∧ p3))) → False)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217557759170000393673258901927 : ((((p3 ∧ False) ∨ p2) → p1) → ((p1 → (((False ∧ p3) ∨ (p4 ∨ ((p3 → True) → (p1 ∨ (False ∧ (p4 ∧ (False ∨ p5))))))) ∨ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668426903271668240176099322308 : ((((((p5 ∧ (((p1 ∧ p4) ∨ (True ∧ (True ∧ ((p5 ∨ p3) ∧ False)))) ∧ ((p4 ∨ p4) ∧ p4))) ∨ p4) ∧ p3) ∨ (p5 ∨ (p3 → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205808038761901840562650235466 : (((p3 ∨ p2) → ((False ∨ False) ∧ False)) ∨ (((p4 → (p5 ∨ p1)) ∧ p2) ∨ (((True → p2) → True) → (True ∨ (True ∨ (p2 ∧ (p3 → p1))))))) := by
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
theorem thm_5_vars_342082595835848588603739661021 : (p2 → ((p3 ∨ (((p1 ∨ ((((((p5 → False) → p5) ∨ p4) → False) ∧ (p3 ∧ (False → p5))) → p3)) ∨ True) ∨ True)) → ((p4 ∨ True) ∧ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783384394857993412043304242169 : (((p3 ∨ ((p5 ∧ (((p1 ∨ False) → p1) ∧ (p1 ∧ ((False ∧ p2) ∧ ((p2 ∨ False) → p5))))) ∨ (False → ((p3 → p2) ∧ (False ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49564797731491124275256839216 : (((((((p5 ∨ p1) → p3) ∧ ((p5 ∨ p4) ∧ True)) → ((p1 ∧ (False ∨ p1)) → p4)) → ((p5 ∨ p4) ∧ False)) → ((p3 ∧ p5) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196733406078102554083211944973 : ((((p4 ∨ (p4 ∧ (p5 → p3))) → False) ∧ p2) ∨ ((False → (((p3 ∧ ((p2 → p2) ∨ (p5 ∨ p1))) ∧ p4) ∨ (p5 ∧ p3))) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172355269074034652364300754567 : ((((p3 ∨ (p2 ∧ (p1 → p1))) ∨ p2) ∨ (((p3 ∧ p3) → p1) → (False ∨ p3))) ∨ (False → ((False ∧ ((p3 → (p4 ∧ False)) ∨ False)) ∧ p4))) := by
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
theorem thm_5_vars_50392704551882425956449037182 : ((((p4 → p3) ∨ (((((False ∨ p1) ∨ p3) ∧ (True ∨ (p2 → (True → True)))) → p3) ∧ (p4 ∧ p3))) ∨ ((True ∧ (True ∧ True)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134466416768000921901827719938 : (((((p4 ∨ p2) → ((p1 ∧ p1) ∧ ((p5 → p5) ∧ (((p2 → p5) ∨ (p3 → (p5 → False))) ∨ p5)))) ∧ p2) → p4) ∨ ((p1 ∨ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152978122219876398019897283110 : ((p1 ∧ ((True ∧ (True ∧ (True ∧ (((p4 ∧ False) → False) ∨ p5)))) ∧ (p5 ∧ (p4 → ((True ∨ p5) → p4))))) → ((p2 → (False ∧ True)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h5.left
    let h14 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h5.left
    let h17 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47335628881105749816738886437 : ((((p4 ∧ p5) ∧ (((((p2 ∨ p5) → p4) ∨ p1) → ((p5 ∧ (p3 → (False → p5))) ∨ (False ∨ (False ∧ p2)))) ∨ p3)) ∨ (True → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78699126546163979737523977068 : (((((p3 ∨ (p5 → ((p1 → (False ∧ p3)) → False))) → (p2 ∧ (False ∨ p5))) ∧ (((False → True) ∧ (p1 ∧ p4)) ∧ True)) ∧ (p3 ∨ True)) → p5) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h12 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h13 : (p3 ∨ (p5 → ((p1 → (False ∧ p3)) → False))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h14 := h4 h13
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h18 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h19 : (p3 ∨ (p5 → ((p1 → (False ∧ p3)) → False))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- Implications on the right can always be decomposed.
      intro h21
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h22 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h23 := h21 h22
      -- We need to get the left conjuct of h23 based on <expert-advice>.
      let h24 := h23.left
      -- False on the left can always be used.
      apply False.elim h24
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h25 := h4 h19
    -- We need to get the right conjuct of h25 based on <expert-advice>.
    let h26 := h25.right
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h27 =>
      -- False on the left can always be used.
      apply False.elim h27
    case inr h28 =>
      -- One of the premise coincides with the conclusion.
      exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742693883418511160188481160109 : ((((p2 → p5) ∨ (((p1 ∨ (p4 ∧ p2)) ∧ p5) ∨ (p3 ∧ ((False → (p4 ∨ ((p1 ∨ ((True ∧ (True → p2)) ∨ p2)) → False))) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48215753039976139442946344664 : ((((False → p2) → ((((p5 ∨ ((False ∨ p4) ∧ ((p1 → False) → p2))) ∨ ((p5 ∨ False) ∧ True)) ∧ (p5 ∨ False)) ∧ True)) → (p3 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662127056407930695664041741712 : (((((((p3 ∨ (p1 → ((p5 ∨ (False ∧ False)) ∨ p2))) ∧ False) ∧ p4) → ((p1 ∧ (p2 ∧ (True → True))) ∨ (p3 → True))) → (p3 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60752207599375222427869854405 : ((True ∧ ((p1 ∨ (p4 ∧ p3)) → (p1 → (p5 ∨ (p3 ∨ ((((True ∧ (((p1 ∧ True) ∨ (p4 ∧ p1)) ∧ p2)) → p2) ∧ p4) ∧ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745437578805479777797978447 : (((p1 ∧ (True → p4)) ∧ ((p4 ∨ (p4 → p1)) ∨ (((p3 ∨ True) ∧ p3) → ((p5 ∨ ((True ∧ p5) → True)) ∨ (p2 → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149827002376635173110588747492 : ((p1 ∨ ((((False ∨ p3) ∨ ((p1 → p4) ∨ (False ∨ ((p3 → True) → p1)))) ∨ (False ∨ p1)) ∨ (False → p3))) ∨ ((p1 ∧ (p4 → p3)) → False)) := by
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
theorem thm_5_vars_110698765110755070606641111849 : ((((((((((p3 ∨ p3) → (p2 ∨ p4)) → p5) ∨ (p1 → (True ∧ False))) ∧ p3) → (False ∨ (p4 → p2))) ∧ p3) ∧ p5) ∧ False) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198352788184279573547312543789 : ((p2 ∧ (p1 ∧ (p4 → (False ∧ (p1 ∨ p3))))) ∨ ((p2 ∧ ((True → p3) ∨ (True → (p2 ∧ p1)))) ∨ ((True ∨ (p2 ∧ p5)) ∨ (p4 ∧ p1)))) := by
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
theorem thm_5_vars_216920120512649434940427250618 : (((p5 ∨ (p3 ∨ p2)) ∧ p3) → ((p2 ∨ ((((p1 ∨ p3) ∧ (False ∧ ((p5 → p1) ∧ True))) → (p2 ∨ (p3 ∧ p2))) → p2)) ∨ (p3 ∨ False))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134917380070024108001251379604 : (((((((p3 → (p3 → False)) → p1) → p5) ∧ (((p3 ∨ ((p2 → True) ∧ p5)) ∨ False) → p1)) ∨ True) ∧ (True ∧ True)) ∨ (p2 → (p3 ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160513156504603250236303517106 : (((p3 ∨ (((p2 → p1) ∨ (False ∧ True)) ∧ ((p5 ∧ True) ∨ p4))) ∧ (p5 ∧ ((p5 ∧ p2) → p1))) → ((p3 → p1) ∨ (p1 ∨ (True ∨ p3)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h3.left
        let h15 := h3.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h3.left
        let h18 := h3.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- False on the left can always be used.
      apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607529905070160514074956132782 : (((((False ∧ (((((((True → True) ∨ p2) ∧ (p3 → p5)) ∧ (p2 ∨ ((p5 ∨ p2) ∨ (p1 ∧ p4)))) → False) ∨ p3) ∧ False)) ∧ True) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_150982141862356672042559446157 : (((p2 ∨ (p5 → ((p1 ∧ (True ∨ (p2 ∨ p4))) → ((p3 ∧ (p3 → (False ∨ (p2 ∧ p4)))) → p3)))) ∨ p2) → ((p5 ∨ p3) ∨ (p3 → p3))) := by
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
theorem thm_5_vars_978573386544893850345060312663 : (((True ∧ (True → ((p2 → (p5 → (p1 ∨ ((p1 → False) → p3)))) ∧ (True → (False ∧ (((p2 ∨ (p1 ∨ p4)) ∨ p1) ∧ (True → p2))))))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165535194745225692124036044291 : (((p5 → ((True → ((p3 → False) → p4)) ∧ (p2 ∨ True))) → (p2 ∧ ((True → p2) ∨ False))) ∨ ((True ∨ p5) ∨ (p5 ∧ ((p2 ∨ False) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47133119856534114023591430892 : ((((False → (p3 ∧ (p2 → (((p3 ∨ p1) → (((p4 → False) → (False → p3)) → p2)) → True)))) → ((p2 → p4) ∨ True)) ∨ (p1 ∧ p1)) ∨ p4) := by
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
theorem thm_5_vars_171626041413031791842741960299 : (((((p5 ∧ p1) ∧ p3) → (p2 → ((False ∧ (False ∧ (p3 → p3))) ∨ p4))) ∨ p4) ∨ ((((p1 ∧ p1) ∧ True) ∧ p2) ∨ (p2 → (False → p5)))) := by
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
theorem thm_5_vars_45864530619403885395045489842 : (((p3 → (((((p4 ∧ True) ∧ p5) ∧ p4) ∨ (True → ((((p4 ∧ False) ∨ p2) ∨ p4) ∧ ((p2 → (False ∧ True)) → p5)))) → p1)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620331147074709068607688961595 : (((((p1 ∨ p4) ∨ ((False ∧ (p1 → (p1 ∧ False))) ∨ ((((p3 ∨ p2) → ((p2 ∨ (p2 → p4)) ∨ True)) ∧ (p4 ∨ True)) ∨ False))) ∨ p5) ∨ False) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136206920931282353690053694066 : (((p5 ∨ (((p2 ∧ p2) ∨ p5) → p4)) ∧ (p2 ∨ (True → (p3 ∨ ((p4 ∨ p5) → ((p2 ∧ (p2 → False)) ∨ p1)))))) ∨ (p2 ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727893367289711983216099548536 : ((((p2 ∨ (p3 ∧ p4)) ∨ (((((p5 → (p4 → (True → p5))) ∧ ((p5 ∧ False) ∨ (True → p2))) ∨ True) → ((p3 ∨ p4) ∧ p1)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257167642900345127799447939284 : ((p2 ∨ p1) → (False ∨ ((((False ∧ p2) → p5) ∨ False) ∧ ((p3 → False) → ((((p3 ∧ (True ∧ p5)) ∧ ((p2 ∧ False) → p2)) ∧ p5) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    -- False on the left can always be used.
    apply False.elim h4
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191072926446705191368472858057 : (((p2 → ((p2 ∨ p3) ∨ p4)) → (p2 ∧ (p4 ∧ p5))) ∨ (((True → True) ∨ (((p4 → (p1 ∧ p4)) ∧ ((True ∨ p4) ∧ False)) ∧ p2)) ∨ p2)) := by
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
theorem thm_5_vars_50411808606575217110813261877 : (((p1 ∧ ((((((((p1 ∨ p5) → p1) ∨ p1) → p1) → p4) ∧ p4) ∧ (True ∨ (p3 → p5))) ∨ False)) ∨ (p1 ∨ ((False ∨ False) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765418800532363525072451330271 : (((p4 ∧ ((p5 ∨ (((((p5 ∨ (p5 ∧ False)) ∨ ((p4 → (True ∨ p5)) ∨ p3)) ∧ False) ∨ True) ∨ p4)) ∧ ((p3 → (False → p2)) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610327436518954451592008265524 : ((((((p3 → (False ∨ (((False → ((False → True) ∨ ((True ∨ True) ∧ (((p2 → p1) ∨ True) → p4)))) ∨ True) ∨ p2))) ∨ p4) → p3) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_208953097359278628028110209566 : ((True ∨ ((p4 ∨ (p4 → p4)) ∨ p5)) → ((((False ∧ ((p2 ∨ (p2 ∨ p5)) → (p5 ∧ p3))) ∨ True) → (p3 ∧ ((p3 → False) → p3))) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : ((False ∧ ((p2 ∨ (p2 ∨ p5)) → (p5 ∧ p3))) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h10 : ((False ∧ ((p2 ∨ (p2 ∨ p5)) → (p5 ∧ p3))) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h11 := h2 h10
        -- We need to get the left conjuct of h11 based on <expert-advice>.
        let h12 := h11.left
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h14 : ((False ∧ ((p2 ∨ (p2 ∨ p5)) → (p5 ∧ p3))) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h15 := h2 h14
        -- We need to get the left conjuct of h15 based on <expert-advice>.
        let h16 := h15.left
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h17 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h18 : ((False ∧ ((p2 ∨ (p2 ∨ p5)) → (p5 ∧ p3))) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h19 := h2 h18
      -- We need to get the left conjuct of h19 based on <expert-advice>.
      let h20 := h19.left
      -- One of the premise coincides with the conclusion.
      exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65316433275983207862120855547 : ((p3 ∨ (((p2 ∨ ((True ∨ (p2 ∧ ((p2 → p3) ∨ p1))) ∧ True)) ∧ (p2 ∨ (((False → p4) ∧ p2) ∧ False))) ∨ (False → (False → True)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_60471292384114895515437509612 : (((p5 → p4) → ((False ∨ ((p3 → p3) → ((False → True) ∧ (((False ∨ p3) ∨ True) → p5)))) ∨ ((((p4 ∧ p4) ∨ p5) → True) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780936047747764203460026456490 : (((p2 ∨ ((p1 ∧ (True → p3)) ∨ (((((((False → p4) ∨ ((True → p3) ∧ (p3 → (p2 → False)))) → p2) ∧ p3) → False) ∨ p5) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263419442009059518443603753292 : (True ∧ ((p4 ∧ ((((p4 ∨ (p2 → p4)) → True) ∨ (p5 ∨ (((p5 ∧ p1) ∧ ((p2 ∨ p1) → True)) → True))) → p2)) ∨ (p4 → (True → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622159489806033941783795431770 : ((((p2 ∧ (((True → True) ∨ True) → (True ∧ ((((False ∧ (p3 → (p3 ∧ p2))) ∧ True) ∨ (((p1 → p3) ∨ True) → False)) ∨ p3)))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_696306907835465462086743164238 : ((((p1 → ((p5 → (p3 ∧ True)) → ((((False → p5) → p2) ∨ True) ∨ False))) → (True → (((p4 ∧ ((p3 ∧ False) ∧ p5)) → p4) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632629378213839140117184221307 : (((((p2 → ((((False → (p1 ∧ ((((p3 ∧ (p2 → True)) → p4) ∧ p4) ∧ False))) ∨ ((p4 ∧ p3) ∨ p3)) → p1) ∧ p3)) → p4) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149206232168720980445045561555 : (((True ∧ p1) ∨ ((p2 ∨ p1) ∧ (p5 → (p4 ∧ ((p4 → ((p3 ∨ p2) ∨ p2)) ∨ (p4 ∧ (p2 ∧ False))))))) ∨ (True ∨ ((p1 ∨ True) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172246803213081954077205324610 : ((((p1 → p4) ∨ (((False → True) → False) ∨ p4)) ∧ (((p5 ∨ p5) ∨ p5) ∧ p2)) ∨ ((False → False) ∨ ((p5 → p5) → (p2 ∧ (False ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117634914567476048374994242879 : ((p3 ∧ ((p1 ∧ (((p5 → (True ∧ ((p1 ∧ p2) ∧ (p4 → (p2 ∧ ((p3 ∧ p5) ∨ False)))))) ∨ (p4 → False)) → p4)) ∨ False)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135886126431081512925796673970 : (((p3 ∨ (p2 ∨ (p3 → (p1 ∧ ((p4 → (p5 → True)) ∨ True))))) ∨ (p2 ∨ ((p2 ∧ (p4 ∧ (p5 ∧ False))) ∨ True))) ∨ ((p5 ∨ p3) → p2)) := by
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
theorem thm_5_vars_178674027857489726802069296438 : (((False ∨ (p5 ∧ (p1 → False))) ∧ ((False → ((p4 → p1) ∧ False)) → p2)) ∨ ((True ∨ p2) ∨ (((p3 → True) ∧ (True → p5)) ∨ (p4 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678137482981830439925527621717 : ((((((p4 → (((False → p4) → p5) ∨ (p2 ∧ p5))) ∨ (True ∧ p2)) ∨ (((False ∧ p2) ∨ p4) ∨ p3)) ∨ (False → (p1 ∧ (p1 ∧ p3)))) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211339547107117202281498791713 : (((p3 ∨ False) ∨ (p1 ∨ True)) ∧ ((p1 → (p2 ∨ (p2 → p5))) ∨ (True ∧ (p5 → ((False ∨ ((False ∧ (p5 ∧ p2)) ∨ True)) ∨ (p1 → p2)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_322501949435271543350183509144 : (p5 ∨ (((p3 → p1) → (((((p1 → p3) ∧ p4) ∧ ((True ∧ p3) ∨ (((False ∧ ((p3 ∧ p2) ∨ p4)) → False) ∧ p5))) ∨ p3) ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184271196577740616034312331415 : (((((p3 ∨ ((False → p3) ∧ p5)) ∨ p4) → (p3 ∧ p4)) → p5) ∨ (p5 → (((p1 ∨ ((True → p4) → (True → (True → p3)))) ∧ p5) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350982399450715492325433732500 : (p4 → (((p3 ∧ p2) ∨ (True ∧ (False ∨ (((p1 ∨ ((p2 ∧ False) → (((p2 ∧ True) → True) ∨ (p1 ∨ p3)))) ∨ True) ∧ p2)))) ∨ (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161526279201561559007846096239 : ((p5 ∧ ((((((True → True) ∧ (p4 ∧ p2)) ∨ (p2 ∧ p5)) ∧ (p5 → True)) ∧ (False ∨ p5)) ∧ True)) → ((False ∨ ((p3 → False) ∧ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h15 =>
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h20 =>
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757319905288360178117946564433 : (((p1 ∧ ((p5 ∨ p3) ∨ ((p2 ∨ ((((False ∧ p2) → p4) ∧ p2) ∨ p1)) → (p1 ∨ (True ∨ (((p5 ∨ False) ∧ (p4 ∧ p2)) → p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121622709983322116532850788640 : (((((p5 ∨ (((False ∧ p3) ∧ p3) ∧ (False → ((p3 → True) → True)))) ∨ (False ∧ True)) ∨ (True ∨ ((p1 ∨ p5) ∧ p5))) → p3) → (p3 ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∨ (((False ∧ p3) ∧ p3) ∧ (False → ((p3 → True) → True)))) ∨ (False ∧ True)) ∨ (True ∨ ((p1 ∨ p5) ∧ p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219115122215026495695933103772 : ((True ∨ ((True → p5) → True)) → ((True ∧ True) → ((p5 ∨ (p1 ∧ (((p4 ∧ ((((p4 ∧ True) ∧ p5) ∨ p2) → p1)) ∧ True) ∧ p2))) ∨ True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156836666135435270751634300677 : (((p1 → ((((p4 → (True ∨ p2)) ∨ p3) ∧ (p4 ∨ p5)) ∧ ((p2 → (p2 ∧ p3)) → p2))) ∧ p5) ∨ ((False → (p1 → True)) ∨ (True → p5))) := by
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
theorem thm_5_vars_303771346091588080425063905534 : (p1 ∨ ((((p2 ∨ p2) → ((False ∨ p5) ∨ ((p5 ∧ (p3 ∨ p1)) → (((p1 ∧ p5) → ((True → (p2 ∨ p4)) ∧ p3)) ∨ True)))) ∨ p1) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



