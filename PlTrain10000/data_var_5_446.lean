variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257014404299389962941370922856 : ((p2 ∨ True) → (((True ∧ ((((False → p4) ∧ (((((True → True) ∨ p3) ∧ p3) ∨ True) → True)) → p3) ∧ p4)) ∨ (p3 → p1)) ∨ (False → False))) := by
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
theorem thm_5_vars_67837426230747059784824074750 : ((p2 → (((((((p2 ∨ p4) → ((p3 → False) ∧ (p5 ∨ False))) → p4) ∨ True) → (False ∨ ((True ∧ p4) ∧ True))) ∨ p5) ∨ (p3 → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113879298088063387347719005482 : ((((p1 ∧ ((p3 ∧ p5) → (((p1 ∧ (p2 ∨ p5)) ∨ p1) ∧ (True ∧ (p4 → (p2 ∨ False)))))) ∧ True) ∧ ((False ∧ p2) → p4)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119184666493959367067481647489 : ((p2 → (((True ∨ ((p1 ∧ ((((((p4 ∨ p2) ∧ p3) → False) ∧ p3) ∧ p4) → p2)) → (p2 ∧ True))) → p1) ∧ (p3 ∨ p2))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633140519648510115699772170086 : (((((p1 ∧ (p2 → ((((p2 ∨ p3) → ((p4 → p2) ∧ (True → ((p5 → p4) → (True ∧ p2))))) ∧ p1) ∧ p1))) ∧ (p5 ∨ p4)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115980983686249806047143779148 : (((((p5 ∨ True) → p4) ∨ False) → ((True → ((p1 ∧ (((p4 ∧ ((p1 → (p5 → p1)) ∨ p1)) → p2) ∨ True)) → p3)) ∧ p3)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172332820037628744787196555076 : ((((True ∨ (True ∨ p3)) ∨ (p3 ∨ p3)) ∧ ((p2 ∨ p1) ∧ ((p3 ∧ False) ∧ False))) ∨ ((False ∨ p5) ∨ (p4 → (((False ∨ p2) ∧ p3) → p4)))) := by
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
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46918251072267362785924656958 : (((((p1 → (False ∧ ((p2 ∨ p4) ∧ p2))) ∧ ((p1 ∧ p1) ∧ (True ∨ (p5 ∧ (p1 → ((p5 ∨ p2) → p4)))))) ∨ p5) ∨ (False → p4)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53711530288442267471398340767 : (((p2 ∨ (p4 ∨ ((p2 → True) ∨ (p3 ∧ (p1 ∧ p5))))) ∧ (((p1 ∨ False) → p1) ∧ (p4 ∨ (p4 ∨ (((p3 ∧ p2) ∨ p2) ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201071348908053130125379571119 : ((p5 ∨ (((p3 → p2) → p5) ∨ (p2 ∧ False))) → ((False ∨ p3) ∨ (False ∨ (False → (p1 ∧ (((True → (p1 ∨ p2)) → p3) → (p2 → False))))))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h3
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h8
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652683922004217551257349766163 : ((((p1 ∨ ((True → (p5 → p2)) ∨ (((p2 ∧ (p5 → (p1 → (True ∧ True)))) ∧ False) ∨ (p3 ∨ ((p2 ∧ p4) → True))))) ∧ (p3 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40122735367795345825115906735 : (((((((p5 ∨ p5) → ((p2 ∧ p5) ∨ False)) ∧ (((p4 → ((p4 → p2) ∨ True)) ∧ p3) ∨ p3)) ∧ (True ∨ (p1 → p3))) ∧ p5) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161407230123462027755151568023 : ((p1 ∧ (p1 ∨ ((p5 ∨ p1) → ((p1 ∧ ((p2 ∨ ((True ∨ (True ∧ p4)) ∧ p2)) ∧ p3)) ∨ p3)))) → (((p3 ∨ p3) → p5) ∨ (True ∨ p3))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118370647977102026862559912610 : ((p2 ∨ (((p3 → (p3 → (p2 → (p5 ∨ ((((p1 ∨ (p5 ∧ False)) ∧ p1) ∧ p2) → p3))))) → p1) → ((p1 ∨ p5) ∧ p1))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56638350511035442684804232796 : ((((True ∨ p1) ∧ False) ∧ (((((False ∨ True) ∨ (((p3 ∧ True) ∧ (False → True)) → (False → True))) ∨ ((p4 → p2) ∨ p5)) → p3) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113636796147289155967677129626 : (((p5 → ((p3 → (False ∧ ((((True → p1) ∨ p3) ∨ (p4 ∨ p2)) ∧ False))) ∨ (((p3 ∨ p4) ∨ p5) → p3))) ∨ (False → p3)) ∨ (p5 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60571589028312864568868370730 : ((True ∧ (((p4 ∧ ((p4 ∧ ((p2 ∧ ((((p4 → p2) ∨ False) ∧ p5) ∨ p3)) ∧ (p4 ∨ p3))) ∨ (p4 ∨ True))) ∨ (False → p4)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49095292460876267030630382541 : ((((((False ∧ p3) ∨ (p2 → False)) → (p5 ∧ (((p2 ∧ (p2 ∨ p1)) ∧ p5) ∧ p2))) ∨ (False ∨ (False → p4))) ∨ (False → (p3 → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117480362619299656303926168770 : ((p1 ∧ (p2 ∨ ((p1 ∧ ((((True ∨ (((p2 ∨ True) ∧ (p4 ∨ False)) ∨ False)) → p5) ∧ (True → (True ∧ p2))) → p3)) ∧ False))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59194461717864650215253707165 : (((p1 ∨ p1) ∨ ((p1 ∧ (((p1 ∨ (p1 → (p3 ∨ p1))) → ((p2 ∨ p2) ∧ (p2 ∨ p3))) → (p3 ∧ p4))) ∨ ((False → p5) ∨ p3))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_213861595263558332941400559021 : (((p1 ∨ (True ∧ p4)) ∨ p3) ∨ (((((True → (True → (p5 → p4))) ∨ True) ∨ p4) ∧ False) ∨ (False → (True ∧ (p5 ∨ (True ∨ (True ∧ p4))))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319068395233684471064674441721 : (p4 ∨ ((p4 → (((p3 ∧ ((((p1 ∨ p3) → (p5 ∨ (p3 ∨ p4))) ∧ (p1 → p2)) ∨ p1)) ∧ p1) ∨ p1)) ∨ (False → ((True ∨ False) → p4)))) := by
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
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168850594422660133367317667609 : ((p3 ∨ (p3 ∧ (p2 → (p2 ∨ ((p3 ∧ ((p5 → p1) ∧ True)) ∨ (p2 ∨ (True ∨ False))))))) → (((False ∧ False) ∨ (p2 ∨ p4)) ∨ (False → False))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175464620693596694835295300293 : ((p2 → (((p3 ∧ p4) ∧ (False → (False ∧ (p4 → ((False ∧ True) ∨ p1))))) → p5)) → (p3 → (p1 → (((True ∨ p4) ∨ p5) → (p5 ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156875269030506222843444866414 : ((((p4 ∨ ((False ∨ ((p3 ∧ (p4 ∧ ((p1 → True) ∧ p1))) → (p5 ∧ True))) → p5)) ∧ p5) ∨ True) ∨ (p1 ∧ ((False → p1) ∧ (False ∧ p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_854566817200306149224256485 : ((p2 ∨ (False ∨ ((p3 ∨ (True → ((p2 ∨ p4) ∨ (p2 → ((p4 ∧ ((p1 ∨ p1) ∨ (p5 → (p2 ∨ p5)))) → p4))))) ∨ False))) ∨ p2) := by
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
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136646073266352965346241659920 : ((((p4 ∨ p3) → p1) → (p2 ∨ (p2 → (((p2 → p2) ∧ p4) → (((p3 → p3) → True) → ((p2 → p5) → p1)))))) ∨ ((p3 → p1) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (p4 ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148586092992520028076492806110 : ((((((p4 ∧ (False ∧ False)) ∨ False) ∨ p2) ∨ (True → False)) ∨ (((p2 ∨ (p3 ∨ (p4 ∧ p3))) ∧ False) → p2)) ∨ (p2 → ((True ∧ p5) ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196905374647238836588543682758 : (((p5 → (True ∨ ((p1 ∧ p4) ∧ p5))) ∧ p2) ∨ (((p1 → (p5 ∨ True)) → (p2 → (((p3 → p4) ∧ p3) ∨ (True ∧ True)))) ∨ (p5 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300784568875481225002116206768 : (False ∨ ((((p5 ∨ p1) → ((True ∧ p5) ∨ False)) ∧ (p2 ∨ (p3 ∨ ((False → p2) ∨ p3)))) ∨ (p4 → ((p2 → (p1 ∧ (p3 → False))) ∨ True)))) := by
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
theorem thm_5_vars_42430005110432008683730200539 : (((p5 ∧ ((p4 → ((p1 ∧ False) ∨ p2)) ∨ (((p1 → ((p1 → p3) → False)) ∨ ((p3 ∨ (p4 ∧ False)) ∨ (p3 → False))) ∧ p4))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749629986565095569812476034738 : (((True ∧ (((((((p5 ∧ ((p5 ∨ (((p2 → p5) ∨ p2) → p5)) ∧ ((p2 ∨ p2) ∧ False))) ∨ True) ∨ False) → p3) → p3) ∨ p5) ∨ p4)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∧ ((p5 ∨ (((p2 → p5) ∨ p2) → p5)) ∧ ((p2 ∨ p2) ∧ False))) ∨ True) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305414253075584983897560818332 : (p1 ∨ (((p3 ∨ p3) → (((p4 ∨ (p3 ∧ ((p1 ∨ False) ∨ (p5 ∨ True)))) ∨ True) → p1)) ∨ (False → (((p3 ∨ (p3 ∧ False)) → True) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733823059046108706469006276484 : ((((p5 ∧ p4) ∧ (((((p1 → p5) ∧ ((True → p3) ∨ (p1 → p4))) → (((p1 ∧ False) → (p2 ∨ (p2 ∨ True))) ∧ False)) → p5) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779476762013513162561618516574 : (((p2 ∨ (((p2 → ((True ∧ ((p3 → (p5 → p4)) ∨ p4)) ∨ (((p1 ∧ p4) ∧ p3) ∧ p3))) → (p1 ∨ (p2 ∧ (False ∨ p4)))) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_36247182390588379359113504001 : ((p4 → ((((((p1 ∨ p5) ∨ (p1 ∧ p1)) ∨ ((((p5 → p1) ∧ (p5 ∧ (True ∨ p1))) → p2) ∨ p2)) ∧ p4) ∨ (False ∨ p2)) ∨ True)) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249414506157439136076961341440 : ((p5 ∨ False) ∨ ((False ∨ (((True ∧ (p5 ∧ ((False ∨ p3) → ((p1 → p4) ∨ (p2 ∧ ((p4 → p2) ∨ True)))))) ∧ (False ∧ p5)) ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761627797049171641790231717169 : (((p3 ∧ ((((p4 ∨ (((p4 → (p4 → p2)) ∧ p2) ∧ (p3 ∧ (p4 → p1)))) ∨ p1) → (((p1 ∨ (p1 → p4)) ∧ p3) → False)) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241517429824329832938020362170 : ((False → p3) ∧ (((((True → True) ∧ False) → (((True → p2) → (p3 ∧ p2)) ∧ ((p1 → False) → True))) → ((p1 ∨ p3) ∨ (p4 → True))) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618051733302856983192783443485 : ((((((True → (True ∧ False)) → p3) ∧ (p4 → (p4 → (((((p1 ∨ (False ∨ p4)) → (p5 ∨ p2)) ∨ True) → (p2 ∨ p2)) ∨ p5)))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715601893771155579744363316803 : (((((p2 ∨ (False ∧ p2)) ∧ p1) ∧ ((p1 → (p2 ∧ p3)) ∧ ((((p2 ∨ ((p3 ∨ p2) → True)) ∧ p3) ∨ p1) ∨ ((p4 ∧ False) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46915195311740103314819704895 : ((((((p2 ∨ (True → False)) ∨ ((False ∧ (p3 → True)) ∧ p1)) → ((p4 → (p4 ∨ True)) ∧ (p4 → (False ∨ p1)))) ∨ p5) ∨ (True ∨ p1)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181191137279559362281515205249 : ((p1 ∧ (False → (((p3 ∧ ((True ∨ False) ∨ p5)) ∨ p2) → (p3 ∧ p4)))) → (((p2 ∨ ((p3 ∨ (False ∧ p5)) → (p1 ∨ p3))) → p2) ∨ p1)) := by
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
theorem thm_5_vars_50220926434471326668027029991 : (((((p1 → p4) ∨ ((((p1 ∧ p5) ∨ False) ∧ (p2 ∨ (True → (p3 ∧ (p1 ∧ False))))) ∨ p4)) ∨ p1) ∨ (((p5 → True) ∧ False) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185084997392556779962896210665 : (((p2 ∨ p1) ∨ (p1 ∨ (p5 → (((True → p5) ∧ p4) → p1)))) ∨ ((p5 → (False → p1)) ∨ (((False → p5) → True) ∧ (p3 ∨ (p1 ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189664857710363435748422115776 : ((p2 ∨ ((True ∧ (p2 → True)) ∨ ((p3 ∧ p5) → p1))) ∧ (p4 ∨ ((p3 ∧ p3) ∨ (p2 ∨ (True ∧ (((True ∧ (p5 ∧ p3)) → True) → True)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
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
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134096951941942604065592471491 : ((((p1 ∨ ((p5 ∧ p2) ∨ (((True → ((p2 ∧ True) ∨ p3)) ∨ p4) ∧ (p3 ∧ (p3 ∨ (p1 → p5)))))) → p4) ∨ True) ∨ (p5 ∨ (p1 ∨ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52565725919517437440117101854 : (((((p1 ∨ (True ∧ p2)) ∧ ((p5 → (p2 ∨ p1)) ∨ p5)) ∧ (False → False)) ∨ (((p2 ∨ False) → ((p5 → False) ∨ p3)) ∧ (True ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230141509139618502489619095316 : (((p4 ∧ p1) ∧ p2) → (p5 → (((p5 ∧ (p5 → False)) ∧ (p3 ∨ (((p3 → (True ∧ p3)) → p1) ∨ (p3 → p1)))) → ((True → False) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
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
      -- Conjunctions on the left can always be decomposed.
      let h20 := h1.left
      let h21 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h20.left
      let h23 := h20.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322414583714378127171978322551 : (p5 ∨ (((p5 ∨ (p1 → ((p5 ∨ (True ∧ p4)) ∧ (p1 ∧ p2)))) ∨ (p1 ∨ (p2 ∨ (((True → p4) ∨ (False ∨ True)) ∧ (True → p5))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219205204634240377654483043219 : ((False ∨ (p5 ∨ (p2 ∧ p3))) → (((p5 ∧ (((True ∨ (True ∨ p5)) → (((p1 ∨ p3) → p2) ∧ (p4 ∨ (True ∧ p4)))) ∧ True)) ∧ True) → p4)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h12 : (True ∨ (True ∨ p5)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h13 := h7 h12
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- One of the premise coincides with the conclusion.
        exact h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h22 : (True ∨ (True ∨ p5)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h23 := h7 h22
      -- We need to get the right conjuct of h23 based on <expert-advice>.
      let h24 := h23.right
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- One of the premise coincides with the conclusion.
        exact h25
      case inr h26 =>
        -- Conjunctions on the left can always be decomposed.
        let h27 := h26.left
        let h28 := h26.right
        -- One of the premise coincides with the conclusion.
        exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69171941921771498072243969275 : ((p5 → ((p1 ∨ ((p3 ∧ (p5 ∨ ((p1 ∨ False) → (False → ((True ∧ p1) ∨ p5))))) ∧ p1)) ∨ (((p1 → p3) ∨ p3) ∧ (p3 → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117651897188626302326556503604 : ((p3 ∧ (((((((p5 ∧ True) ∧ p4) ∨ (False → (((p3 ∨ True) ∧ p5) ∨ (p3 ∧ p4)))) ∨ True) → p4) ∧ p3) ∨ (p1 → False))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250717135844152166001160407976 : ((p1 → False) ∨ (((p2 ∨ p2) ∨ p5) ∨ (p2 ∨ ((p4 ∨ (True ∨ (p2 → ((False ∨ False) ∨ p4)))) ∨ ((p5 ∨ (p3 ∨ (p3 → p2))) → True))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181288517356848061047339145818 : ((p5 ∧ (((((p5 ∨ p3) ∨ True) → (True → False)) → (p2 → p2)) → True)) → (((((p1 ∧ False) ∨ (p3 ∨ p1)) → p5) ∧ (True → False)) → p4)) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712907887097955988448036058934 : ((((True ∧ ((True ∨ p2) → (p4 ∧ True))) ∨ (((p1 ∨ ((p1 ∧ True) ∨ (p4 ∧ (p2 ∧ p3)))) ∨ p2) ∨ (False ∨ (p4 ∨ (p4 → True))))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_349710805649915798500263699428 : (p4 → ((((p3 ∨ ((False ∧ ((p2 → ((p4 → p5) ∨ p4)) ∧ False)) ∨ p3)) → p5) → ((p5 ∧ ((False ∧ p2) ∧ p5)) ∨ (True ∨ True))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109646227628837988958895325699 : ((p4 ∨ (((((p4 ∧ (p3 → ((p1 → p3) → p1))) → ((p1 ∧ (p2 ∧ (p4 → (p4 → p2)))) ∧ p2)) ∧ p2) → False) ∨ True)) ∧ (p5 → True)) := by
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
theorem thm_5_vars_105738433538750011188289691319 : ((((p2 ∧ p5) ∧ (((p2 ∧ p3) ∧ True) ∨ ((p5 → (False → (False ∨ p3))) ∧ p2))) ∨ (((p1 ∧ False) ∧ p3) → (p1 ∨ p1))) ∧ (True ∨ False)) := by
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
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113858101778277149463847365038 : (((p2 → ((p1 → (True ∧ (p2 ∧ ((p1 ∨ (((p1 ∧ p1) → (True ∨ (p4 ∨ p3))) → p1)) ∧ p5)))) ∨ p3)) → (False ∨ p3)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618698835149668792104719232288 : ((((((p2 ∨ True) ∨ p4) ∧ (p5 ∧ ((p2 → ((True ∨ False) → ((((p4 ∨ (p3 ∨ (p2 → p3))) ∨ p2) → p3) → p1))) ∧ True))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_45830645742166234996370561755 : (((p2 → (((((((p3 → (p4 ∨ True)) ∧ p4) ∧ p1) ∨ False) ∧ (p5 ∧ (p2 ∨ p4))) ∧ (p5 ∨ p1)) ∨ (p3 ∨ (False → False)))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217911030784112463307962803067 : (((p4 → (p1 ∨ p3)) → False) → (((((True ∨ p4) ∨ (p3 ∧ p2)) ∧ (p5 ∧ ((False ∧ p1) ∨ p3))) ∨ (p1 ∧ ((p1 → False) → True))) → p2)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h5.left
        let h9 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- False on the left can always be used.
          apply False.elim h11
        case inr h13 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h14 : (p4 → (p1 ∨ p3)) := by
            -- Implications on the right can always be decomposed.
            intro h15
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h13
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h16 := h1 h14
          -- False on the left can always be used.
          apply False.elim h16
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h5.left
        let h19 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- False on the left can always be used.
          apply False.elim h21
        case inr h23 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h24 : (p4 → (p1 ∨ p3)) := by
            -- Implications on the right can always be decomposed.
            intro h25
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h23
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h26 := h1 h24
          -- False on the left can always be used.
          apply False.elim h26
    case inr h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- Conjunctions on the left can always be decomposed.
      let h30 := h5.left
      let h31 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h32 =>
        -- Conjunctions on the left can always be decomposed.
        let h33 := h32.left
        let h34 := h32.right
        -- False on the left can always be used.
        apply False.elim h33
      case inr h35 =>
        -- One of the premise coincides with the conclusion.
        exact h29
  case inr h36 =>
    -- Conjunctions on the left can always be decomposed.
    let h37 := h36.left
    let h38 := h36.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h39 : (p4 → (p1 ∨ p3)) := by
      -- Implications on the right can always be decomposed.
      intro h40
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h37
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h41 := h1 h39
    -- False on the left can always be used.
    apply False.elim h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135107043958458623118700328322 : ((((p4 ∧ (False ∧ p5)) ∧ (((p4 ∨ (p1 → p5)) ∨ ((p5 → True) ∧ (p3 ∨ (False → False)))) → p2)) ∨ (p3 → True)) ∨ (p4 ∨ (False ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_867491480108362921379522186897 : (((((p1 ∧ True) ∨ ((p1 → (((p4 ∧ (p2 → True)) ∨ True) → ((((p3 ∨ p3) → (p1 → p3)) → p4) ∧ p3))) ∨ (True ∨ p5))) → p5) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∧ True) ∨ ((p1 → (((p4 ∧ (p2 → True)) ∨ True) → ((((p3 ∨ p3) → (p1 → p3)) → p4) ∧ p3))) ∨ (True ∨ p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299490463181947194705327160675 : (False ∨ ((p3 → (((((p4 ∧ (True → ((p5 → (p3 → ((p4 ∨ True) ∧ p5))) ∨ p2))) ∧ ((p5 ∨ p1) → p3)) → p4) ∨ p3) → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135425602333308849616075500199 : (((p5 ∧ ((p4 ∨ (((((p5 ∧ p2) → False) → p2) → p5) ∧ p5)) → (p5 ∧ (p4 ∧ p1)))) ∨ (p4 → (p5 ∧ p5))) ∨ (p3 → (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157005963457046648429887836392 : ((((p2 ∧ (p2 ∨ p2)) ∧ (((False ∧ ((p3 ∨ p5) ∨ p4)) ∧ (p5 ∧ p3)) ∨ (p1 → p2))) ∨ False) ∨ (((p2 ∨ (p3 → True)) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655352083603533421884514063132 : ((((((((((True ∧ (p4 → (((p5 → p4) → p2) ∧ p4))) ∨ (False ∨ p2)) ∨ True) ∧ p3) → p1) ∨ False) ∨ (p3 → p2)) ∨ (True ∨ p5)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_344116618855742089235762306333 : (p2 → (False ∨ ((p1 ∧ ((True → ((p4 ∧ True) ∨ (p3 ∧ (False ∧ (False ∧ False))))) ∨ ((p1 ∧ ((False → False) ∧ p4)) ∧ p5))) ∨ (False → False)))) := by
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
theorem thm_5_vars_262374917150636766327701115427 : (True ∧ (((False ∨ True) ∧ ((((p1 → ((p2 → p4) ∨ (p4 ∨ (p2 ∧ p5)))) → ((p3 ∨ p1) ∧ (p2 ∧ False))) → p2) ∨ (p4 → p1))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51303292459583013760966126299 : (((p1 ∨ ((((p2 → (False ∧ (p4 ∨ p4))) ∨ (False ∧ False)) ∧ (p4 ∨ (p1 → p2))) ∨ p2)) ∨ (p4 ∨ (p1 → ((False → p5) ∨ False)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200830226289301516043638451187 : ((p5 ∧ (p4 → (True ∧ (p2 → (False ∨ p1))))) → (((p3 → (p1 → p4)) ∧ ((p5 ∨ True) ∨ ((p3 ∧ (p5 ∧ p4)) ∨ p4))) ∨ (p5 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57974865014793090680841578326 : (((p3 → (True → p4)) → ((p3 ∨ ((((p3 → (True ∨ p1)) ∨ (p2 ∨ p5)) → p1) ∧ ((True → ((False ∧ True) → True)) ∧ False))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150321334073870682863823387553 : ((p4 → (p5 ∨ (p5 ∨ (((p4 ∨ p4) → (False ∧ (((p3 ∨ p3) → False) ∨ ((p1 → p1) ∧ p1)))) ∧ p3)))) ∨ (True ∧ ((p1 ∨ False) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_260821074058331895999222549194 : ((p3 → p5) → (p5 → (((p4 ∨ (p4 ∧ True)) → p2) ∨ (p2 → (p2 → ((False → p3) ∨ ((p1 ∨ (((p3 → p5) ∧ p3) → p3)) → p4))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157974119983903003510427916302 : (((p2 ∨ ((((p2 ∧ False) ∧ p4) → p3) → False)) ∨ ((p5 ∨ p1) → (p3 ∧ (p4 → (True ∨ p5))))) ∨ ((((p4 ∧ False) ∧ p2) ∨ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713834857148994869016649452322 : (((((((p3 → p5) → p2) → p2) ∨ True) → ((((p2 ∧ ((p4 ∨ False) ∨ (p1 ∧ (p4 ∨ (p1 ∨ p3))))) ∧ (p3 → p5)) ∧ False) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205161085899540618133271704176 : (((p3 ∧ (p2 ∧ p2)) ∧ (p4 ∨ p4)) ∨ ((p4 ∨ True) ∨ ((((False ∨ False) ∨ (True ∨ p2)) → (((p3 → (True → p3)) → True) ∨ p1)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136987856047835666245372611086 : (((p5 ∧ True) → ((((p4 ∨ p2) → False) ∨ ((False → True) → (p3 ∨ p5))) → (((p1 → (True ∨ True)) → False) ∧ p5))) ∨ ((p5 ∨ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40345033514826749669321512877 : (((((p2 ∨ (((False ∨ (True ∧ p2)) ∨ p1) → ((False ∨ p3) ∧ ((False → True) ∧ (p4 ∨ ((p1 ∧ p5) ∧ p1)))))) ∨ True) ∨ p1) ∨ p4) ∨ p4) := by
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
theorem thm_5_vars_608347740771781226768425679190 : (((((((p3 → p4) ∨ ((p4 → ((p2 → (((p2 → p3) ∧ (p5 ∧ p5)) ∧ (p4 → False))) ∨ False)) ∧ (p1 → True))) ∨ p1) ∨ False) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345064741845162121211824223854 : (p3 → (((p5 ∨ ((p2 ∧ (p5 → ((p1 ∨ (p1 ∨ ((p4 → True) → (True ∨ p4)))) ∨ p1))) → False)) ∨ ((False ∧ (p5 ∧ p1)) → p2)) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135896985348800685456126038261 : (((((((p1 ∧ p2) → p3) ∨ (p2 ∧ p2)) ∧ (True ∧ p2)) ∨ p5) → (True ∧ (p1 ∧ (((False ∧ True) ∨ p1) ∨ p4)))) ∨ (True ∧ (p1 → True))) := by
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
theorem thm_5_vars_184592574106013855719779365078 : (((False → ((True ∨ (p2 ∨ p2)) → (p5 → True))) → (p3 ∨ p1)) ∨ (True ∨ (False ∧ ((False ∨ p3) ∨ (False → (p5 ∧ (p1 ∨ (p5 → p1)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165960826813783025212324118652 : (((True → p5) ∧ (False ∨ ((p4 ∨ ((p4 → ((False → p1) ∧ p2)) → (p5 → p4))) ∧ p4))) ∨ (p4 → (((p1 ∧ p5) → (True ∨ p1)) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309363645965690525380256251747 : (p2 ∨ (((((False ∧ p2) ∨ p4) → False) ∨ ((p4 ∨ (p4 ∧ p1)) ∨ (p1 ∨ (((p4 → ((True → False) ∨ True)) ∨ True) ∨ p3)))) ∨ (p5 ∧ True))) := by
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
theorem thm_5_vars_190688323119446589873492076636 : (((((False → (p4 ∧ p2)) ∧ False) ∧ True) ∧ (p4 ∧ False)) ∨ (((False ∨ p1) → (True ∧ ((((False ∧ p2) ∨ True) → p1) ∧ p5))) → (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40094916289298835518594988752 : (((((p1 ∨ ((p5 ∨ p2) → ((p1 ∧ ((((p3 ∧ False) ∨ (p3 ∨ p4)) ∧ ((p4 ∧ p5) ∧ False)) → p1)) ∧ p3))) → p2) ∧ p2) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166912977995488176144765170091 : ((((p3 ∨ ((False → p3) ∧ (p3 ∧ p5))) → ((p1 ∧ p4) ∨ ((p2 ∧ p4) → p5))) ∧ p5) → ((((p3 ∨ (p1 ∨ p4)) ∨ p3) ∨ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637516917560742620897182256598 : (((((((p2 ∧ p2) ∨ ((p2 ∧ (p1 → p3)) ∧ p1)) ∧ p3) ∨ ((((p2 ∧ (p3 → (p3 ∨ False))) → p3) ∨ True) ∨ (True ∨ p1))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68081179126656473594907209069 : ((p2 → (p3 ∨ (p4 → ((((p2 ∧ (p5 ∧ (p3 → p5))) ∨ (((((False → (p1 ∨ p2)) ∨ p1) ∧ p5) ∨ True) → False)) ∨ False) ∨ True)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227711783479537924357048988388 : ((p1 ∧ (p3 ∧ p2)) ∨ ((((p5 → p5) → p2) ∧ (((p5 ∨ True) ∨ p5) ∨ (p5 → (False → ((p3 → p5) → (p5 ∨ p1)))))) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159098669082862613459283407852 : ((True → (((p1 → False) ∨ p4) ∧ ((p2 → ((p5 ∨ (p1 ∧ (False ∧ p1))) ∧ p2)) ∧ (p5 ∧ p1)))) ∨ (True ∨ (((p1 ∨ True) ∧ p4) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113807671892487552280619753879 : (((True ∧ (p5 → ((p3 → (True ∨ (p5 → p4))) ∨ (((p3 ∨ (p2 ∨ p5)) ∨ False) ∨ (p5 ∧ (p5 ∨ p4)))))) → (True ∧ p1)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671523357837623344820405194549 : ((((p3 → (p5 ∨ (False ∧ ((p1 ∨ p2) ∨ ((((((True ∧ False) ∨ p4) ∨ True) → True) ∧ (p1 ∨ p1)) ∨ p3))))) ∨ ((p4 ∨ p4) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56381573309473379774233816233 : (((((True ∨ p3) ∨ False) → p2) → ((p2 ∨ p1) → ((((p5 ∧ (False ∧ (True ∨ ((p5 ∨ p5) → False)))) → p5) → p1) ∨ (True ∨ p1)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114737509929703047872830536381 : (((((p5 ∨ p3) → p4) ∧ (((p3 ∧ True) → False) → (p1 ∨ (True ∧ (p1 → False))))) → ((p4 → (p3 ∧ p2)) → (False ∧ p1))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336136518240673935372858998192 : (p1 → (((p5 ∧ ((p3 ∨ ((((((((p2 → p2) ∧ True) → (False → p1)) ∧ True) ∧ p3) ∧ p2) ∧ p1) ∧ p2)) ∨ (p5 → p2))) ∨ p1) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89364100659031102712374599175 : (((True → (p2 ∨ p2)) ∧ (((False ∨ p3) → (p1 ∨ False)) ∨ (p3 ∧ (((p4 ∨ True) ∨ (p3 ∧ (False ∨ p2))) ∧ ((p5 → True) ∨ p3))))) → p2) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h16 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h17 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h18 := h2 h17
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- One of the premise coincides with the conclusion.
            exact h19
          case inr h20 =>
            -- One of the premise coincides with the conclusion.
            exact h20
        case inr h21 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h22 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h23 := h2 h22
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h24 =>
            -- One of the premise coincides with the conclusion.
            exact h24
          case inr h25 =>
            -- One of the premise coincides with the conclusion.
            exact h25
      case inr h26 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h27 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h28 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h29 := h2 h28
          -- Disjunctions on the left can always be decomposed.
          cases h29
          case inl h30 =>
            -- One of the premise coincides with the conclusion.
            exact h30
          case inr h31 =>
            -- One of the premise coincides with the conclusion.
            exact h31
        case inr h32 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h33 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h34 := h2 h33
          -- Disjunctions on the left can always be decomposed.
          cases h34
          case inl h35 =>
            -- One of the premise coincides with the conclusion.
            exact h35
          case inr h36 =>
            -- One of the premise coincides with the conclusion.
            exact h36
    case inr h37 =>
      -- Conjunctions on the left can always be decomposed.
      let h38 := h37.left
      let h39 := h37.right
      -- Disjunctions on the left can always be decomposed.
      cases h39
      case inl h40 =>
        -- False on the left can always be used.
        apply False.elim h40
      case inr h41 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h42 =>
          -- One of the premise coincides with the conclusion.
          exact h41
        case inr h43 =>
          -- One of the premise coincides with the conclusion.
          exact h41



