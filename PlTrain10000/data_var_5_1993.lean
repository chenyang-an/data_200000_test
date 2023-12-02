variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180590311066896731900424018814 : (((p4 ∨ ((p3 ∧ (p3 → (p5 ∧ p1))) ∧ p1)) → ((p3 → False) ∨ p1)) → (p3 ∨ ((p5 ∨ p3) ∨ (False → ((p1 → False) → (p1 → p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106771817544904485846611831752 : (((p4 → (p2 → ((p1 → False) → p1))) ∨ ((((False ∧ p4) → (p1 → True)) → (True → p3)) ∨ (True ∨ (p1 ∨ (True → p3))))) ∧ (p1 → p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43229847741080277994221610938 : ((((p1 ∨ ((p5 ∧ (((p2 → p2) ∨ (True ∨ ((p3 ∨ ((p5 → False) → (p2 ∧ True))) ∨ p4))) → (p3 ∨ p3))) → p5)) ∧ p2) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357533035792074395148813082711 : (p5 → (True ∧ (p3 ∨ (((((p4 ∨ False) ∨ True) ∨ True) ∧ ((p5 ∧ p3) → ((((True ∨ (p2 → p3)) ∧ (p1 ∨ p1)) ∨ p3) ∨ p5))) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186708336061021920974247504412 : ((((p4 ∨ (p1 ∨ p4)) ∧ (p1 → p5)) ∨ (p5 ∧ (p3 → p5))) → ((p1 ∨ (True ∧ (((p2 ∨ True) ∨ p3) ∨ p4))) ∨ ((p4 → True) ∨ p4))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260285427858287936520679510090 : ((p2 → p4) → ((p4 ∨ ((((False ∨ (p4 → (p3 ∨ ((p3 → True) ∧ p1)))) ∧ p3) → ((p5 ∨ p1) ∨ ((p5 ∨ p3) → p2))) ∨ True)) ∨ p3)) := by
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
theorem thm_5_vars_608885407111328442081795745958 : ((((((False → (True ∨ (((((True ∧ p5) ∨ (False ∧ p1)) ∨ p2) ∧ (False → p5)) ∨ p2))) → (((False → True) → p5) ∨ p1)) ∨ True) ∨ p2) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_695709418689230202959930624977 : (((((True → (p4 ∧ (p5 ∧ p3))) ∨ (((True ∧ p3) ∧ (p3 ∨ p2)) ∧ True)) → (True ∧ (False ∨ (((p5 ∨ p2) ∨ p3) ∨ (True ∨ p2))))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
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
theorem thm_5_vars_149007019666856931795875236982 : ((((p1 ∨ p2) ∧ p5) ∨ ((p1 → ((p2 ∨ True) → ((True ∧ (p1 ∧ ((p4 ∧ True) ∨ p5))) ∨ p3))) ∨ True)) ∨ (p1 → (p4 → (False ∧ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135650970550002807882754062275 : ((((p5 → (p4 ∨ (p3 ∧ (p1 ∨ p4)))) ∨ (((p1 ∨ False) → p3) ∨ (p3 ∧ False))) → (p1 ∨ ((p5 ∧ p1) ∨ True))) ∨ (p1 ∨ (p5 → p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197695742549673665030679600025 : (((p4 ∨ (p1 → (p3 → True))) → (p2 ∧ p4)) ∨ (((((p1 → ((p4 → p4) ∨ p3)) ∧ False) → p5) → p3) → (p3 → (p2 ∨ (p3 → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337357137857917177764857578761 : (p1 → ((((((((p2 → p3) ∧ (p2 ∨ (p4 ∨ p1))) → p5) ∧ (False ∨ p3)) → False) ∨ (False → p2)) ∨ (p2 → False)) ∨ ((p2 ∨ p3) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590965699689653521518975276517 : (((((p1 → (p5 ∨ (((p4 → p2) ∨ True) ∨ (p3 ∨ ((((p2 → (True ∧ (False ∧ (p4 ∧ True)))) ∨ p5) ∨ False) → p3))))) → p2) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786415605661695392036210432540 : (((p4 ∨ (((((p2 ∨ p5) ∨ (((p4 → p5) → False) → (p4 ∧ p3))) → p5) ∨ True) ∨ (p4 ∨ (p3 → ((p2 ∧ (p1 ∨ p4)) ∨ p1))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69052352079171013763592693757 : ((p5 → ((p3 ∧ (p3 ∧ (((((p3 ∨ p5) ∧ p3) → True) → ((p1 ∨ p4) ∧ ((p1 → p4) ∧ (p5 ∧ (p5 ∨ True))))) ∨ True))) ∨ p5)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_437334791429641883757913860080 : ((((p3 ∧ ((True → (p2 ∧ (p5 ∧ (False → p3)))) ∧ (p2 ∧ (p1 → (((p5 ∨ p1) → (p1 ∨ p4)) → (False → p4)))))) → (p3 ∧ p2)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h11.left
  let h13 := h11.right
  -- One of the premise coincides with the conclusion.
  exact h12
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65836491575515160853768957850 : ((p4 ∨ ((p5 → ((True → p3) ∨ p4)) → ((((p1 → p2) ∨ True) ∧ True) → (p5 → ((p4 ∨ (((p3 → p3) → p1) ∧ p5)) ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732307066249218702415031017824 : ((((False ∧ False) ∧ ((True ∧ p3) → ((p2 → p1) ∧ ((p4 ∨ True) → (p1 → (False ∧ (True → ((True ∨ (False ∧ (False ∧ False))) ∨ p2)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157078766896389927613521671390 : (((p3 ∨ (((((p5 ∧ p1) ∨ p3) ∧ ((p4 ∨ p2) ∧ (p2 ∨ (False ∨ p2)))) → p5) ∧ p4)) ∨ p5) ∨ ((False → p1) ∨ ((False ∧ p5) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351404917172501353088155426118 : (p4 → (((((p3 ∨ ((p4 ∧ p5) ∧ True)) ∧ (p2 ∧ (p4 ∧ p4))) ∨ p3) → (p1 → ((p3 ∧ p5) ∧ p5))) ∨ (p3 → ((p4 ∨ p2) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117208243066169426058465784700 : ((True ∧ (((p3 → p5) ∧ (True ∧ (True ∧ p4))) ∨ (((p2 ∧ False) ∨ True) → ((((p1 → p5) ∨ (p5 ∧ p3)) ∨ p3) → p1)))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154735940854581000065475852948 : (((((p2 ∨ ((False → False) ∧ p2)) → (p1 ∧ (p5 ∨ True))) ∨ ((False ∧ False) ∨ True)) ∨ (p1 ∧ p3)) ∧ (((p1 → p2) ∨ False) → (True → True))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656956867609084792490548488975 : (((((((p2 ∧ p2) → p3) ∨ p1) → ((p5 ∧ ((p4 ∧ True) ∧ (p4 → (False ∧ (p1 ∧ (p1 ∨ p3)))))) → (p5 ∧ False))) ∨ (False ∨ p1)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the left can always be decomposed.
  let h11 := h2.left
  let h12 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h12.left
  let h14 := h12.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h13.left
  let h16 := h13.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h17 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h18 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h19 := h14 h18
    -- We need to get the left conjuct of h19 based on <expert-advice>.
    let h20 := h19.left
    -- False on the left can always be used.
    apply False.elim h20
  case inr h21 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h22 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h23 := h14 h22
    -- We need to get the left conjuct of h23 based on <expert-advice>.
    let h24 := h23.left
    -- False on the left can always be used.
    apply False.elim h24
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159296296209192945262273811484 : ((p4 → (p3 ∨ (((((False ∧ p2) ∧ (p3 ∧ True)) ∨ p2) ∨ (p3 → (p4 ∨ False))) ∨ (p1 ∨ False)))) ∨ ((p4 → ((True → False) → p3)) → p3)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648932237941513926342647084674 : ((((((((p5 ∨ p5) ∨ (p4 ∧ ((True → False) → p2))) ∨ ((((p2 ∧ p4) → p4) ∨ p3) ∧ (p4 → True))) ∨ True) → False) ∧ (p2 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55302662687600482590414141424 : (((p5 ∧ (((p1 → p3) ∧ p2) ∨ p2)) ∨ ((True ∧ (False ∨ (p1 ∧ ((p1 ∨ (False → p5)) → (p1 ∨ p3))))) ∨ (p5 → (p2 ∨ p5)))) ∨ p1) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55946040521946890000066638719 : (((p4 → ((True ∧ p5) ∨ False)) ∧ (p3 ∨ ((True ∧ (p2 → ((((p2 → (p1 ∧ p3)) → (True ∧ (False ∧ True))) ∨ p2) → p3))) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759707834889287939940011380178 : (((p2 ∧ ((((False ∨ True) → True) ∧ (p4 → (True ∧ ((p5 ∧ True) ∨ p5)))) ∨ ((p5 ∧ ((p4 → False) ∧ ((True ∧ p4) → p1))) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117460339987987176585903994566 : ((p1 ∧ ((p5 ∨ p5) ∨ (((p2 → ((False ∨ p1) ∧ (p1 ∧ ((p4 ∧ p4) ∨ ((p1 ∧ p5) ∨ p5))))) ∧ False) ∨ (False ∨ True)))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190683942841081487916008918659 : (((p5 → ((True ∧ (p4 ∨ (True ∨ True))) ∧ p2)) → p5) ∨ (False → (p1 → ((((p4 ∧ (p2 → p3)) ∨ p3) ∨ (p4 ∨ (True ∨ p5))) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351828742048960515027270892061 : (p4 → ((p3 ∧ (p1 ∨ ((True ∨ (p2 → (p5 ∧ (p3 → True)))) ∨ p5))) ∨ (p1 ∨ ((p4 → p4) → ((p1 ∧ p3) ∨ ((p3 ∨ p4) ∨ p2)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166502419831101373660974986226 : ((p3 ∨ (p4 → ((((p2 → ((p5 ∨ p4) → True)) → (p5 ∧ False)) → p1) → (False ∧ False)))) ∨ (((p5 ∨ ((p1 ∨ p5) → p3)) ∨ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134761133652970967064374733394 : ((((p1 ∨ p3) → (p3 → ((p2 ∨ (((True ∨ p3) ∨ True) → p5)) → (p4 → ((p4 ∧ False) ∨ (p1 → p1)))))) → p3) ∨ (True ∨ (p2 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60189349064422500798918530891 : (((p5 ∨ p3) → (((True ∨ (((((p5 ∧ True) ∨ p1) → ((p1 ∨ True) ∨ (p2 ∧ (True ∧ True)))) → p1) ∨ p3)) → False) ∨ (True ∨ p1))) ∨ p3) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165218383250879347766577577613 : (((((p2 ∨ (False → (p5 ∨ False))) ∨ (p3 ∧ False)) → ((p3 ∧ p5) ∧ p3)) ∨ (p4 → False)) ∨ ((p4 ∧ (p3 ∨ p5)) → ((True ∨ p3) → p4))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157681029874603246658599896027 : (((p1 ∧ ((p3 ∨ True) → (((((p4 ∨ True) ∨ p1) → True) ∨ p5) ∧ p4))) ∨ (p2 ∨ (False ∨ p3))) ∨ (p1 ∨ (p3 → ((False ∨ p5) → True)))) := by
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
theorem thm_5_vars_63336948765528254297480791554 : ((p5 ∧ ((p4 → p3) → ((False ∧ (((p4 → p5) → p3) → False)) ∨ (((p1 ∧ p4) → (p4 ∧ (p4 → p3))) ∧ ((p1 ∨ p2) ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204320489340475665999459759680 : (((p2 ∧ (p5 ∧ (False ∧ p1))) ∧ True) ∨ ((((((p2 ∨ True) → (p4 ∨ p4)) ∧ (p1 ∧ p1)) → ((p2 ∨ (True ∨ p1)) → p3)) ∨ True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299252180442437258681792494095 : (False ∨ ((((p3 ∨ (((p3 ∨ p3) ∧ ((((False → (p4 → True)) → p2) → False) ∨ True)) ∧ True)) → False) ∧ ((p4 → p3) ∧ (p3 ∨ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42569339207133056159852988699 : (((p2 ∨ (((p4 ∧ ((p5 ∨ (p2 ∨ ((p3 ∧ (p2 ∧ p1)) ∧ (True ∨ True)))) ∨ (p3 ∧ (p2 → p2)))) ∨ (p4 ∨ p3)) ∨ p5)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68830062325313471513459959221 : ((p4 → ((True → (True → p5)) → ((((False ∨ p2) ∨ (((p5 ∧ p2) ∨ (p1 ∧ p4)) ∧ True)) ∨ p5) → ((False ∨ (p1 → p3)) ∨ True)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704401163103585716041927321689 : (((((False ∨ (True ∨ p3)) ∧ (p1 → ((True → False) → p4))) → (False ∨ (((False ∨ (False ∨ (False ∧ True))) ∨ ((p4 ∧ p5) → p5)) ∨ p3))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258884858851762173592789516501 : ((True → p2) → (((((p5 → ((True ∨ False) ∨ ((p4 → (p4 ∨ False)) ∧ p5))) → (((False → (p5 → True)) ∨ p2) ∧ p4)) → p2) → p2) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742694706724596846584972574246 : ((((p2 → p5) ∨ (((False ∧ False) ∧ p4) ∧ ((((p3 ∧ p3) ∧ (True ∨ ((p1 ∧ (p5 → (True → p4))) ∧ (True → p4)))) ∨ p3) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174512940870083978836816004497 : (((p5 ∧ ((False ∧ True) ∧ (False ∧ False))) ∨ ((False ∨ ((p2 → False) ∨ False)) ∧ p4)) → ((p5 ∧ ((p1 ∨ (False ∨ False)) ∧ (p1 ∨ False))) ∨ p4)) := by
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
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h15 =>
        -- False on the left can always be used.
        apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159093346033253395213614831443 : ((True → ((p3 ∨ ((p4 ∧ p3) ∧ ((p2 ∨ p5) ∨ (p1 ∨ p4)))) ∧ (p5 ∨ (p4 ∨ (False ∨ True))))) ∨ (((p3 ∧ p2) ∧ p2) → (p3 ∧ True))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245223604925553097153851005248 : ((p2 ∧ p1) ∨ ((True ∧ ((p4 ∨ p4) ∧ ((p3 ∧ ((((p4 ∧ True) → False) ∧ (False → p3)) ∧ p5)) ∨ (((p1 → p1) → p5) ∨ p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160844439588224680356385395575 : (((((p3 ∧ p3) ∧ p1) ∨ p3) ∧ (((p4 ∨ p3) ∨ (False ∧ ((p2 → p4) ∨ p1))) → (p5 → p2))) → ((p5 → (p4 → (p3 → False))) ∨ True)) := by
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
theorem thm_5_vars_138497772416865656401936116273 : (((((p3 ∨ p4) ∧ ((p4 ∧ p4) ∨ (((p4 ∨ p5) ∨ ((p1 ∧ p5) ∨ p1)) ∨ (True ∧ (True ∨ False))))) ∧ True) ∧ p2) → ((p1 ∨ p1) ∨ p2)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
        case inr h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
            -- Conjunctions on the left can always be decomposed.
            let h19 := h18.left
            let h20 := h18.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h21 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
      case inr h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h26 =>
          -- False on the left can always be used.
          apply False.elim h26
  case inr h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h31 =>
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h32 =>
        -- Disjunctions on the left can always be decomposed.
        cases h32
        case inl h33 =>
          -- Disjunctions on the left can always be decomposed.
          cases h33
          case inl h34 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h35 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
        case inr h36 =>
          -- Disjunctions on the left can always be decomposed.
          cases h36
          case inl h37 =>
            -- Conjunctions on the left can always be decomposed.
            let h38 := h37.left
            let h39 := h37.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h40 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
      case inr h41 =>
        -- Conjunctions on the left can always be decomposed.
        let h42 := h41.left
        let h43 := h41.right
        -- Disjunctions on the left can always be decomposed.
        cases h43
        case inl h44 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h45 =>
          -- False on the left can always be used.
          apply False.elim h45



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194007956850581026555182076916 : ((p4 ∨ ((p4 ∧ (p4 ∨ ((p3 ∨ p1) ∨ p3))) → p2)) → (True → ((((True ∧ (p4 → p3)) ∧ p2) ∨ True) ∨ ((p2 ∧ False) → (False → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189219224404013219726264336457 : (((p4 ∨ p5) ∨ ((p5 → p5) ∨ (p3 ∨ (p1 → p1)))) ∧ (p4 → (((p2 ∧ (False → ((p1 → p2) → (p2 → p4)))) → False) ∨ (False → p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173066814724704039134581960360 : ((False ∨ (p2 ∧ (((((False → (False → p3)) ∨ p4) ∨ p1) → (p1 → False)) ∧ p1))) ∨ ((p5 ∧ (True ∨ ((p4 → p5) ∨ True))) → (p5 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792913808424014737953594006227 : (((True → ((p2 ∧ p1) ∧ (((((p3 ∧ True) → ((p4 → ((p4 → (p1 ∧ p2)) ∧ p1)) ∧ True)) ∨ (p3 → (p5 ∨ p2))) → p2) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115875243775910875837487464572 : (((((True → p4) → True) ∧ p3) ∨ (p2 → ((p2 ∧ (p1 ∨ p4)) → ((p2 → ((p3 ∧ (p5 ∧ False)) ∧ p5)) ∨ (p1 ∨ True))))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228967583992680971420035640321 : ((p4 ∨ (p2 → p4)) ∨ ((False ∧ (p4 ∧ p5)) ∨ ((p2 ∨ ((((p4 ∧ p4) → p1) → True) ∨ (p4 ∨ (p3 ∧ p1)))) ∧ ((p2 ∨ p5) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_972152810068176196858589717302 : ((((True ∨ p3) → ((((((((p1 ∧ (p5 ∧ p3)) → p4) → p1) ∨ True) ∧ ((True ∧ p5) → (True ∧ p1))) ∧ (p1 ∧ p2)) ∧ p1) ∧ True)) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p3) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160269906579880881051174044761 : (((p1 → (((p3 → p2) ∨ (((((p4 ∧ p3) ∧ p5) ∧ p4) → p2) ∨ p5)) ∨ True)) ∨ (p3 ∨ p2)) → (p4 ∨ ((p4 → p3) → (p1 ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753641481370073983537988128957 : (((False ∧ (((p1 ∨ (((p2 → p5) ∧ (p2 ∧ ((p1 ∨ p1) ∨ p2))) → p5)) → (p1 → True)) → (True → (((p2 → p5) → p4) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161789112464974324937920659837 : ((p5 ∨ (((p4 ∨ p3) ∧ (p3 ∧ (p3 ∧ ((((p3 ∨ (p3 ∨ p2)) ∧ p2) ∧ p3) ∨ True)))) ∧ p5)) → (p4 ∨ (((False → False) ∨ p5) ∨ False))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Conjunctions on the left can always be decomposed.
        let h16 := h14.left
        let h17 := h14.right
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h18 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h8
          case inr h21 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h8
      case inr h22 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h7.left
      let h25 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- Conjunctions on the left can always be decomposed.
        let h29 := h28.left
        let h30 := h28.right
        -- Conjunctions on the left can always be decomposed.
        let h31 := h29.left
        let h32 := h29.right
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h33 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h34 =>
          -- Disjunctions on the left can always be decomposed.
          cases h34
          case inl h35 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h5
          case inr h36 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h5
      case inr h37 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217914905185026656664071137855 : (((p4 → (p1 → p5)) → p4) → (p3 → ((((p5 ∧ p4) ∧ (((((False ∨ p3) ∨ ((False → False) → p4)) ∧ p2) ∨ True) → p1)) ∨ True) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114115798501147950518042380484 : (((p4 ∨ ((((False ∨ ((p3 ∨ p4) ∧ ((p4 ∧ p4) ∨ p4))) ∨ (p1 → (p1 ∧ p2))) ∨ p3) ∨ True)) ∨ (p5 ∧ (False ∧ p3))) ∨ (True → p1)) := by
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
theorem thm_5_vars_223594058014189641426580664099 : ((p1 ∨ (True ∨ False)) ∧ ((p4 ∧ (((p1 ∧ (p3 → True)) ∨ (p4 → p4)) → (((p2 ∨ False) → p4) ∨ (p4 → (p5 → p4))))) ∨ (False → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246337874174281517961301195740 : ((p4 ∧ p5) ∨ ((((True → ((p1 ∧ False) ∨ p5)) ∧ (p4 ∨ p3)) ∨ True) ∨ (p5 → ((False ∨ ((((False ∧ True) → True) ∧ p1) ∨ p5)) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342597399857443057144247607394 : (p2 → ((((p2 → p3) ∧ (p4 ∨ (p2 ∧ (False → (p3 → p3))))) → p4) → (((((True ∧ p4) ∧ False) ∨ p4) ∨ ((p5 → False) ∨ True)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115213506576542610020228154100 : (((p3 ∨ ((p2 ∧ p1) ∨ ((p2 ∧ p4) → (False ∨ True)))) ∧ (((p2 ∨ (p4 ∨ True)) ∧ p3) ∨ ((True ∨ (True ∧ p4)) ∨ p5))) ∨ (p5 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46683699910062774624467843893 : (((p2 ∨ (((((p4 → ((False → True) → p1)) ∨ True) ∧ p1) → (False ∨ p4)) → (p1 → (True ∧ (p2 → (p4 ∨ False)))))) ∧ (p2 → p2)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (((p4 → ((False → True) → p1)) ∨ True) ∧ p1) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171312681045700214889929445581 : ((((p4 → (((p1 ∨ (p5 ∧ ((p3 ∨ p1) ∨ p2))) ∨ p3) ∧ p5)) ∧ p4) ∧ p3) ∨ (True → (((p4 ∨ False) → p4) ∨ ((p1 ∨ False) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602110733123077524221880217948 : ((((p5 ∧ (((p4 ∨ ((p4 ∨ (p4 ∨ (True → p2))) → (p1 ∧ False))) → p3) ∧ ((p1 → False) → (True → (p5 ∧ (p3 ∨ p2)))))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630660718121743469061584764284 : (((((False → ((((p3 → True) ∨ True) ∧ ((p3 ∧ ((False → p5) ∧ p1)) → p3)) → ((True → (p1 → (True ∧ p3))) → p5))) ∨ p5) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114919978231396399285822729047 : (((((True → ((True ∧ p3) ∧ (p4 ∨ p2))) ∨ (False ∧ (True ∨ False))) → False) → ((((True ∧ p1) → p4) ∧ p3) ∧ (p1 ∧ p3))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133526339345283676216285731213 : ((((((((p2 ∨ False) ∨ (p5 ∧ (p5 ∨ p4))) → True) → ((p4 ∧ p2) ∧ False)) ∧ ((p2 → p3) ∨ p2)) ∧ p1) ∧ True) ∨ (p3 ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207940477589134397864239473634 : (((True → (p2 ∨ p3)) ∧ (False → p4)) → ((p3 → (((True → p5) ∨ p5) → (((((False ∧ p3) ∧ p2) ∧ p1) ∧ p2) ∨ p2))) ∨ (p1 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137905792504169951403694837593 : ((p4 ∨ (((((p4 ∨ (p3 → p4)) ∨ p2) ∨ (True ∨ True)) ∨ True) ∧ (((p3 → (False ∧ True)) ∧ True) ∨ (p1 → False)))) ∨ (p3 → (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113819945628699404029287600916 : (((p3 ∧ (p1 → ((p5 → ((((p2 → True) ∧ (p3 → (((p1 → p4) ∨ p5) ∧ True))) ∧ True) ∨ p1)) ∨ p5))) → (p5 ∧ p3)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41080002075680818359916733599 : (((((((False → p1) → (p1 ∨ (p5 → (True ∨ (p4 → (((p1 ∧ True) → p1) ∨ p5)))))) ∧ p1) ∧ p3) ∧ ((p3 ∧ p4) ∧ p4)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57983708870094516217714789239 : (((p4 → (p2 ∨ p3)) → ((((p1 ∨ (((((p3 ∧ p2) ∨ True) → p5) → p5) ∧ p2)) ∨ p5) ∧ (p1 ∨ ((p4 ∨ False) ∧ p5))) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307304167973490457904266274023 : (p1 ∨ (p3 ∨ (((p4 → p1) ∧ ((False ∨ p1) → (((True ∨ p4) ∧ (p4 ∧ False)) ∨ (((p4 ∨ (p4 ∨ p5)) ∧ (True → True)) ∧ p3)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350184651678198527247327406059 : (p4 → (((p3 ∨ (False ∧ (p2 ∧ p3))) ∨ (((False ∨ p2) ∧ p3) ∨ (False ∧ (((p2 → (p1 ∧ False)) ∧ (p4 ∧ (p5 ∧ p3))) → False)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356663625533545538937023194956 : (p5 → (((p5 ∧ True) → (((True → p4) ∧ True) ∧ p2)) → (((p2 → False) ∧ (p1 → (p5 ∨ ((True → ((p4 ∧ p4) → p5)) ∧ False)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40951415556328053878251949747 : (((((((True ∨ (p3 ∨ ((((p4 → (False ∧ p5)) ∧ (True ∧ p1)) ∨ p5) ∧ True))) ∨ p3) ∧ p2) → (p1 → p3)) ∨ (p2 → p2)) ∨ False) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137016155838328922243660148360 : (((p2 ∨ p3) → ((p2 → (((p4 ∨ ((False ∨ (p5 → p3)) ∧ p4)) ∧ ((p1 ∧ p5) ∧ (p3 ∧ p2))) ∧ p3)) → p2)) ∨ (False ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173180686112487594148011550006 : ((p4 ∨ (((p3 ∨ (p2 ∨ True)) → p1) → ((((p4 ∧ p4) ∨ True) → p1) ∧ p1))) ∨ ((p4 ∧ ((False ∨ (p1 ∧ False)) → p3)) → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612521789087209419221667027612 : (((((((p3 ∧ (p3 ∨ (p5 ∧ p2))) → (True → (((True ∧ ((True → p4) → (False → False))) → p5) ∧ False))) ∨ p1) ∨ (p1 → p1)) ∨ p3) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_230720622982087805376803784857 : (((p5 → True) ∧ p2) → (True → (((p1 ∧ (p4 → (False ∧ ((((p3 → ((p2 ∧ (p5 ∧ True)) → False)) ∧ False) ∨ p3) ∧ False)))) ∨ True) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_821406004673296711367503270172 : ((((((p3 → ((p2 ∨ p2) ∧ p2)) → (p1 ∧ ((False → (p3 → True)) ∨ p1))) ∧ ((p5 ∧ p5) → ((False → (False ∨ p3)) ∧ p4))) ∧ p2) → p1) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p3 → ((p2 ∨ p2) ∧ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158178165313767300351808503827 : ((((False ∨ p1) → (True ∧ p3)) → (p5 ∧ (True → (((p2 → p4) ∧ ((True ∨ True) → p4)) ∨ p4)))) ∨ (False → (p4 ∧ (p1 ∨ (p2 ∨ p5))))) := by
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
theorem thm_5_vars_779364168587980529089150704075 : (((p2 ∨ (((((p2 ∨ (p1 ∧ p5)) ∨ (p4 ∧ (p3 ∧ ((True → False) → ((True → (p3 → p1)) → p2))))) ∧ (p4 ∨ False)) ∧ True) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_135084635186339307316292889052 : ((((((((p3 ∨ p5) → (p2 ∨ p4)) ∨ False) → p4) → (p5 → p3)) ∧ (((p1 → p4) → p4) → p2)) ∨ (p5 → p2)) ∨ ((p5 ∧ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51703927837071093069825402483 : ((((((p5 ∧ p2) ∧ (((True → p1) ∧ p5) ∧ p3)) → p2) → ((p3 → p5) ∧ p2)) ∧ (((True ∧ (p1 ∨ (p4 ∨ p2))) ∨ p3) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766405889270298004251243613404 : (((p4 ∧ (False ∧ ((p4 ∧ ((p4 ∨ (((((p1 ∧ False) ∧ p3) ∧ False) → p3) ∨ ((p3 ∨ p4) ∧ p1))) → p5)) ∨ (p5 ∧ (p5 → True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208859435438520588165880970471 : ((p4 ∧ ((p3 ∨ (p1 ∨ p3)) ∨ p2)) → (((p3 ∧ (p3 ∧ p4)) ∨ ((p5 ∨ False) → p5)) ∧ (p4 ∧ ((p5 → p5) → (p1 ∨ (p4 → True)))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h5
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h10 =>
          -- False on the left can always be used.
          apply False.elim h10
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h11
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h11
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h22 =>
        -- One of the premise coincides with the conclusion.
        exact h16
  case inr h23 =>
    -- One of the premise coincides with the conclusion.
    exact h16
  -- Implications on the right can always be decomposed.
  intro h24
  -- Conjunctions on the left can always be decomposed.
  let h25 := h1.left
  let h26 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h26
  case inl h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h29
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h31
      case inr h32 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h33
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h34 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h35
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39940966798238638575330796951 : (((p3 → (p2 → ((((((p2 ∧ p4) ∨ p1) → ((((p4 ∨ p5) ∧ p4) ∧ False) ∨ p2)) ∨ (p5 ∨ True)) ∧ (p5 → True)) → p5))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300867788978729639280490530607 : (False ∨ ((((((p3 ∨ True) ∧ (p3 ∧ (False → p5))) → p2) → (True → p3)) ∨ p1) ∨ (p5 → ((True ∨ p5) ∨ (p5 → (p4 → (p5 ∨ p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774715629180770790220002577898 : (((False ∨ (((p4 → p3) ∧ (p5 ∨ ((p3 ∨ p5) ∧ p1))) ∨ (p2 ∨ (((((p1 ∨ p2) ∧ True) ∧ (p2 → p1)) ∧ True) ∨ (p5 → True))))) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53239673399112192300709621843 : ((((p3 ∧ (p1 ∧ p2)) ∨ ((p5 → p3) ∨ (p3 → (p1 → p5)))) ∨ (((p1 ∨ p1) → (p3 ∨ (((p5 ∨ p4) ∨ True) → p1))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678705298018642324203388821892 : (((((p2 → False) ∨ (False ∧ (((((p2 → (p2 ∧ True)) ∧ p5) ∧ True) ∧ p2) ∧ (p1 ∨ (p4 ∨ p4))))) ∨ (((False ∧ p2) → p1) ∨ False)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672428572395197274579863618643 : ((((((p4 ∧ True) ∨ (((False ∧ (p3 ∨ (False → False))) ∧ (((p5 → False) ∧ (p3 → True)) ∧ p2)) ∧ p4)) → p1) → (p5 ∨ (p4 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137059050400888847236928279681 : (((p2 → p2) → (((p4 ∧ True) ∨ ((p4 ∨ ((False → False) → p3)) ∧ p5)) → ((p2 ∧ (p4 → p1)) ∨ (True ∧ True)))) ∨ ((p2 → p5) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337773404079193689495304824681 : (p1 → (((p4 ∧ p3) ∧ ((p2 ∧ p3) ∧ ((((p2 ∨ p4) ∨ (p3 ∧ p1)) ∧ p2) ∨ p1))) ∨ (((p3 ∧ ((False ∨ p1) ∧ p1)) → p1) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322487187764087314275166460192 : (p5 ∨ (((p3 ∨ False) ∨ (((p4 ∨ (p4 → (p4 ∧ ((((p4 → True) ∧ p1) ∨ False) ∨ (False ∧ (p5 ∧ p4)))))) ∨ (True → True)) ∨ False)) ∨ p3)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



