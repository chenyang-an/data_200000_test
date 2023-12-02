variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328705926033895944580220063078 : (True → (((p4 ∧ ((p1 → p2) ∧ p4)) ∨ ((False ∨ (p3 ∧ p3)) ∧ p3)) ∨ (p4 → ((False ∧ ((p2 ∨ True) ∨ p4)) ∨ ((p5 ∧ False) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186056519978116797465654895378 : (((((((p2 ∨ p3) → p2) → p3) ∨ (False → False)) ∨ p5) ∨ p3) → ((p4 ∧ (True → p1)) → (((p2 ∨ False) ∨ p5) ∨ ((True ∧ p2) → p2)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h17
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185481485564226686480521356614 : ((p1 ∨ (p3 ∨ (p5 → (((False → p2) ∨ (False → True)) → False)))) ∨ ((True ∧ (False → p4)) ∨ (p4 → (True → (((p2 ∨ p1) → p3) ∨ True))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67784880532348623882025873861 : ((p2 → ((p4 → (False ∧ (((p2 ∨ (True ∨ ((p5 ∧ p1) ∧ p3))) → ((((p5 ∧ (p1 → p3)) ∧ False) ∨ False) → True)) → p1))) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792925288759757092421336170358 : (((True → ((p5 ∧ p1) ∧ (p5 → ((p5 → (p1 ∧ (p4 → (False ∧ (p4 ∧ ((True ∧ ((p1 → False) ∧ (p4 → p5))) → p4)))))) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146498911065119932032508030781 : ((p4 ∨ ((p2 ∧ ((False → ((p3 → (p2 → (p1 → p1))) → p3)) → (False ∨ False))) ∨ (True → (False → p3)))) ∧ (p4 → ((p5 → p4) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693779833621946847393899582882 : ((((((p4 ∧ (p3 → (p4 ∧ ((p4 → (p3 ∨ p5)) → p3)))) ∨ p2) → p5) ∨ (((True ∧ False) ∧ p2) → (False ∧ (True ∨ (p4 ∧ True))))) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41124628555850575425941369194 : ((((((p1 ∨ ((False ∨ (((p5 → ((p1 → True) → p1)) → p1) ∨ p4)) ∨ p2)) ∧ (p1 ∧ p5)) ∧ True) ∨ (p5 → (p5 ∨ p1))) ∨ p5) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234420639589741542903507828125 : ((p2 → (True ∧ p2)) → (True → ((p3 ∧ (True → (((p1 → p2) ∨ p4) ∧ p3))) ∨ (p5 ∨ ((((p5 → (p2 ∨ p5)) → p4) ∧ False) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185518823074650082468015952167 : ((p3 ∨ ((((((p2 → True) ∨ p3) → p5) ∨ p5) ∧ p4) ∨ False)) ∨ (((p2 ∧ p5) ∧ p2) → ((p2 → (True → p5)) ∨ ((p4 ∧ p5) → p3)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251862453951048050961246551752 : ((p3 → p5) ∨ ((True → ((p2 → (((p3 ∧ (p3 → (p1 ∧ p4))) → p2) ∨ False)) ∧ p1)) → (p2 → ((p3 → ((True → p2) → p1)) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20164196668397111261945786948 : (((((((p3 → ((p5 → p2) ∨ p4)) ∧ True) → (False ∧ False)) → p5) ∨ p2) ∨ ((p3 ∨ (p1 ∨ ((p2 ∨ False) ∨ True))) ∨ (p1 → p5))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_41848458657929992455654967700 : ((((p2 → (False ∨ p5)) ∧ ((((p5 → p3) ∨ p1) ∨ (False ∨ ((p2 ∧ p3) → (p5 ∧ (((False ∧ False) → p3) ∧ p5))))) ∨ p2)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198218026188235446175642192459 : ((True ∧ ((True ∨ ((p3 ∨ p2) ∨ p5)) ∧ p5)) ∨ (((p1 → ((False ∧ False) ∧ ((p1 ∨ ((p3 → p3) → p1)) ∨ True))) ∨ False) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674434211933107367768082754460 : ((((p3 ∨ ((((((p4 ∨ (p2 → (p1 ∧ (p3 → p2)))) → (p2 ∨ False)) → False) → p4) → False) → (True ∨ False))) → (p5 ∧ (False ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40910453158005924092488629433 : ((((p5 ∧ ((p2 ∨ (p1 → (True ∧ True))) → ((p1 ∧ p3) ∨ (p1 → ((p4 ∨ p5) ∨ ((p5 → p4) ∨ True)))))) ∧ (p2 → p1)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208776202129233814497808114827 : ((p2 ∧ ((p2 → False) ∧ (p5 → p5))) → ((((p5 → True) ∧ ((True → (True ∨ (p3 ∨ (p2 → p5)))) ∨ True)) → p5) ∧ ((p5 → p5) ∨ True))) := by
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
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h17 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h18 := h15 h17
    -- False on the left can always be used.
    apply False.elim h18
  -- Conjunctions on the left can always be decomposed.
  let h19 := h1.left
  let h20 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h21 := h20.left
  let h22 := h20.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616609421038859897387885169093 : (((((((p5 → p2) → p1) ∨ (p3 ∧ ((True ∨ p5) ∧ p4))) ∧ ((((False ∧ p2) ∧ (p2 ∨ True)) → (p3 ∨ p5)) → (p5 ∧ p3))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219501187926896747336893490160 : ((p5 ∨ ((False → p2) ∨ p1)) → ((p1 ∨ (p5 ∧ (p4 → (True ∧ p1)))) ∨ (p4 → (((p3 ∧ False) ∧ ((True ∧ p4) ∨ (False ∧ False))) ∨ True)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789690264823965104958584231768 : (((p5 ∨ (((True ∧ p1) ∨ (p5 ∨ (False ∨ p5))) → ((p5 ∧ (p5 ∨ (p1 → True))) → (((True ∨ False) → True) → (p3 → (p4 ∨ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172483697736314600671996807812 : ((((p2 ∨ p1) ∨ (p4 ∨ True)) → (((p5 ∨ True) ∧ p1) ∨ ((False ∧ p5) → p4))) ∨ ((p3 ∨ ((p4 ∨ False) ∨ p2)) ∧ (p5 ∧ (p3 ∨ True)))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h5
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
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
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261197002899061565174264144348 : ((p4 → p5) → ((p5 → (((((p3 ∨ p2) ∨ p2) ∨ True) → p3) ∨ (((True ∨ (p5 → p2)) ∧ (p4 → (p5 ∧ p2))) ∨ (p3 ∧ True)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61077893430406496255974690832 : ((False ∧ (((False ∨ p1) ∨ ((p2 → (False ∨ (((p1 → False) ∨ p5) ∨ (p1 ∨ True)))) ∧ (p3 ∧ True))) ∧ (((p2 ∧ False) → p4) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175226971662075007876913337282 : ((p1 ∨ (((False ∧ (p3 ∧ (True ∧ ((p3 ∧ False) ∨ p1)))) → True) ∨ (p5 ∨ p3))) → ((p3 ∧ False) ∨ ((False → True) ∨ (p4 ∧ (p2 → p5))))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716716501863087443118707012203 : (((((p1 → p2) → (False ∧ True)) ∧ ((((((False ∧ p1) → ((p2 ∨ (False ∨ (False ∨ p5))) ∧ p4)) ∨ p1) ∨ p3) ∧ p1) ∧ (p2 ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157761207172068526520191766455 : (((False ∧ (False ∧ ((p3 ∧ ((p5 ∧ (p5 → p5)) ∨ p5)) ∨ p3))) ∧ (((p5 ∧ p4) → p5) ∨ p4)) ∨ (p1 ∨ ((p5 ∧ True) → (True ∨ p1)))) := by
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
theorem thm_5_vars_104601623071229099627300908573 : ((((p3 → ((False ∧ (p5 → (p3 ∨ False))) ∧ p5)) → (((True ∨ (p1 ∨ True)) ∨ p1) → ((p1 ∨ p2) ∨ True))) ∨ (p5 ∨ p4)) ∧ (p4 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111565452579739236376771243021 : (((((((p4 ∨ p1) ∨ False) ∨ p4) ∧ (p5 → ((((p2 ∨ ((p5 → False) → p3)) → p5) ∧ (p4 ∨ False)) ∨ p2))) ∧ p3) ∨ True) ∨ (p4 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63190582741583190722593502514 : ((p5 ∧ (((True ∧ ((((True ∨ p5) ∨ p5) → (p3 → (p1 ∧ p3))) ∨ (p1 ∧ False))) → ((p4 ∨ p1) ∨ False)) ∨ (p3 ∨ (p2 ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42141685317225209780667883638 : ((((p5 ∨ True) → ((p2 → (p5 ∧ ((p4 ∧ (p2 → ((True ∨ True) → p5))) ∨ p1))) ∨ (((p3 → p5) ∨ True) ∧ (False → p5)))) ∨ p3) ∨ False) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115875792156892140610680503508 : (((((p5 → False) → p5) ∧ p2) ∨ (((((p1 ∧ (p2 ∨ ((p5 ∨ p4) → (p4 → True)))) ∨ p3) → (p2 → p4)) ∨ False) → p4)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351254733760423729138052403090 : (p4 → ((p1 ∧ ((((p2 ∨ True) ∨ (True ∨ ((p5 ∧ p1) ∨ (p3 ∨ ((p1 ∧ p1) ∨ p1))))) ∧ p2) ∨ (p2 ∨ p2))) ∨ (p4 ∨ (p2 ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159230297133988696977391464600 : ((p3 → (((((p1 ∧ False) → (True ∧ (False → p1))) ∨ (p4 ∨ (p3 → (p5 ∨ False)))) ∧ p1) ∨ p5)) ∨ ((True ∨ p2) ∨ (p5 → (p1 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196835645704867576286112669220 : (((p4 ∧ (((p2 → p2) → False) ∧ p3)) ∧ p5) ∨ (p1 → (((p5 ∨ p5) ∨ (p5 → (p1 ∨ (p5 → p3)))) → ((p5 ∧ (p3 ∧ False)) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171924742080368518485954455136 : ((((((p5 ∨ (p2 ∧ True)) ∧ (p5 ∧ p4)) ∨ (p5 ∨ False)) ∧ p3) ∧ (p1 ∨ p2)) ∨ (p4 ∨ (p1 ∨ ((p2 ∨ p4) → ((p5 → True) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192147157181474178981860093609 : ((p5 → (p4 → ((p3 ∧ p3) ∧ (p5 → (p1 ∧ p4))))) ∨ (p1 ∨ ((((p5 ∨ (p4 ∨ p5)) → (False → p1)) → p2) ∨ (p4 → (False → False))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622695157404342604903259472779 : ((((p4 ∧ ((((False ∧ p5) ∨ False) ∧ p3) ∨ ((((True → p5) → p2) ∧ ((True ∨ (p3 ∧ p4)) ∨ (p4 ∨ True))) → (True ∧ True)))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135047663523554742632270458746 : ((((((False ∧ p5) → (p4 ∧ ((p5 ∨ p4) ∧ (p2 → p2)))) → ((True ∨ (False ∧ False)) ∧ p5)) ∨ True) ∨ (p3 ∧ p2)) ∨ ((p2 ∨ p4) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_902348079261877952380649780822 : (((((((((False ∨ p4) ∨ p1) ∧ (True ∧ p1)) → p5) ∧ (p2 ∧ p4)) ∧ (True → (p4 ∧ (p5 ∨ p5)))) ∧ (p5 ∨ (p4 ∨ (p3 ∨ p4)))) → p5) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h14 := h5 h13
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h20 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h21 := h5 h20
        -- We need to get the right conjuct of h21 based on <expert-advice>.
        let h22 := h21.right
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- One of the premise coincides with the conclusion.
          exact h23
        case inr h24 =>
          -- One of the premise coincides with the conclusion.
          exact h24
      case inr h25 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h26 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h27 := h5 h26
        -- We need to get the right conjuct of h27 based on <expert-advice>.
        let h28 := h27.right
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h29 =>
          -- One of the premise coincides with the conclusion.
          exact h29
        case inr h30 =>
          -- One of the premise coincides with the conclusion.
          exact h30
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147399290922968538400802650309 : ((((p4 ∨ (p1 → ((True → p5) ∨ p2))) ∧ (True → ((p3 ∨ (p3 ∨ (p4 ∧ p4))) → (p4 ∨ p2)))) ∨ True) ∨ (p5 ∧ (p1 ∧ (p5 → p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313368605879566235652552781002 : (p3 ∨ ((p4 → (p4 ∧ (p2 ∨ (p4 ∧ (p1 ∨ (((False ∨ p4) ∨ ((p4 → p5) ∧ (p5 ∨ ((p2 → True) ∨ p4)))) → (p5 ∨ True))))))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
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
theorem thm_5_vars_172052332011529708539320636599 : (((((p5 → p5) ∧ (p1 → (p5 ∨ ((p5 → False) ∧ p5)))) ∧ p2) → (p4 ∨ p5)) ∨ (p4 ∨ (((p4 ∨ (p5 → (p1 ∨ p3))) → p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178312702797605818476806204438 : (((((p5 ∨ p3) ∨ (((False → p1) → False) ∨ p5)) ∨ p3) ∨ (p5 → True)) ∨ ((((False ∨ ((p1 ∨ p2) ∨ (False ∨ p5))) ∨ True) → p2) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627188945922727453374819409343 : (((((((((p3 ∧ p4) ∧ False) ∨ ((p1 ∨ ((((p1 ∨ p4) ∨ False) → (False ∨ p5)) ∨ p5)) → p1)) → (p3 ∨ p5)) ∨ p2) ∧ p5) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711641330630569641085330660638 : ((((p3 → (p3 ∧ (p2 → (True ∧ p3)))) ∧ ((p1 → ((p5 ∨ (p4 → p5)) ∧ (False ∨ (p2 ∨ (p3 ∧ p4))))) ∧ (p2 ∨ (p1 ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797020563111219980580608393035 : (((p1 → ((((p3 → (((p5 ∨ p4) ∧ False) ∧ ((p5 ∧ p5) ∨ ((False → (p4 → False)) ∧ (False ∨ p5))))) ∧ p3) ∨ (True → p3)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115996808500306378636067269462 : ((((False ∨ (False → True)) → False) → (((p2 ∧ ((p5 ∨ ((p3 ∨ (p4 → (p1 → p2))) → p3)) ∨ p3)) ∧ (True ∧ p1)) ∧ p5)) ∨ (p3 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ (False → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (False ∨ (False → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (False ∨ (False → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h8
  -- False on the left can always be used.
  apply False.elim h10
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : (False ∨ (False → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h11
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252068800199252718223071511296 : ((p4 → p1) ∨ (p3 ∨ (((True ∧ p1) → p3) ∨ ((p4 ∨ p2) ∨ (((p2 ∨ (((True ∧ p1) ∧ ((p2 ∨ p4) ∨ p1)) → p5)) → True) ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684759801534230007324453447369 : (((((p2 ∧ False) ∨ ((((p1 ∨ p4) → (p2 ∨ (p5 ∨ p2))) → (p1 ∨ p5)) ∨ (p5 ∧ p4))) ∨ ((False ∧ (p2 ∨ False)) → (p3 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689995675205639336681235090373 : ((((p1 ∧ (False → ((((True ∨ (False ∧ p3)) ∨ False) ∨ p3) ∧ (p1 ∧ (p5 ∨ p3))))) ∨ (((p4 ∨ p5) ∧ (True → (p2 ∨ False))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747797056132976884949414549427 : ((((False → p2) → (((((((p4 ∨ (p1 ∨ True)) ∧ p3) ∧ p3) → (p1 → p3)) ∨ ((p2 → p2) ∨ p3)) ∨ ((p5 → p2) ∨ False)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135111851013697397397256285636 : ((((p1 → (p4 ∧ p1)) → (True → ((p4 ∧ (p2 → ((p4 ∧ p1) ∨ ((p5 ∧ p1) → p4)))) ∨ p2))) ∨ (p5 ∨ p4)) ∨ (p5 → (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736054312710114012860038417624 : ((((True → p4) ∧ (p5 ∨ ((p5 ∨ (((p2 ∨ ((p5 ∨ ((p2 ∧ p5) ∨ True)) → p4)) ∨ (p1 → (p5 → False))) ∨ (p2 → p1))) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628119466306717819458332619514 : ((((((False → (p4 ∧ p5)) ∧ (p1 → (((p2 ∧ (p4 ∧ p5)) ∨ p3) ∨ (((p1 → False) → (p5 → p4)) ∨ (p5 ∨ p4))))) ∧ p4) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85180462132480979308771566787 : (((((p5 ∨ (p5 → p4)) → True) ∨ ((p3 → ((False ∨ p2) ∨ p5)) ∧ False)) → ((True ∧ True) → (((p1 → (False → p1)) ∨ p3) ∧ p2))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∨ (p5 → p4)) → True) ∨ ((p3 → ((False ∨ p2) ∨ p5)) ∧ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (True ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44815967631121547859093763647 : ((((p1 ∨ (p2 ∨ True)) ∧ ((True ∨ p1) → ((((True → p2) ∨ (p3 ∧ ((((p1 ∧ p4) ∨ p4) → p2) → p5))) ∧ True) ∧ p3))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138266812536481252956915918109 : ((p2 → (p1 → ((((False → p3) ∧ ((((p1 → (p5 ∨ False)) ∨ p4) ∧ (True ∧ p4)) ∧ (False ∧ p4))) ∧ p1) ∨ p1))) ∨ ((p2 → p4) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744665823191415758857900153527 : ((((p3 ∧ True) → ((p3 ∧ p1) ∨ (((p3 → (p3 → (p5 ∧ (p5 ∨ ((p2 ∨ True) → ((p3 ∧ p1) ∧ (False ∨ True))))))) ∧ p2) ∨ p3))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134747688361305369830934446438 : ((((False ∨ True) ∨ (((((((False → True) ∧ (False → p5)) ∧ True) ∧ p3) ∧ p1) ∨ (p2 ∧ p3)) ∨ (p5 ∨ False))) → p2) ∨ ((False ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40877824907527921869580052381 : (((((((p4 ∧ False) → (((p4 ∧ ((True ∧ False) ∧ (p1 → p2))) ∧ p1) → p4)) → False) ∨ ((p5 ∨ p5) → True)) ∧ (False → False)) ∨ p2) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138850250692271149319607780993 : (((True ∨ (p5 ∧ ((p5 ∧ p3) ∧ ((True → (((True ∧ p4) ∧ ((p1 ∧ (p4 ∧ p3)) ∨ p5)) ∨ False)) ∨ p5)))) ∧ p2) → (False ∨ (False ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50238935861490511753953150166 : ((((((True → p5) ∧ ((((((True ∧ p5) ∨ p1) ∨ (p4 ∨ p2)) → True) → p5) ∧ False)) → True) → p2) ∨ (True ∨ (True → (True → p2)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136682092746409906977859383540 : (((p2 → (p1 ∨ p1)) → (p3 ∧ (((p1 ∨ p2) ∨ (p3 ∧ (True → True))) ∧ (((p4 → p5) ∧ (p3 ∧ p4)) → p1)))) ∨ (p4 ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133785225955735704456907263030 : (((((p2 → p1) ∨ p5) ∧ (p3 → (((p5 ∧ (p1 ∨ (p1 ∧ ((p1 → p4) ∨ (False → p3))))) ∧ True) ∨ False))) ∧ p2) ∨ ((True ∨ p2) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122245640848148565301976866250 : ((((p1 ∨ (p4 ∧ p1)) ∨ ((((True → (p1 ∧ (True ∧ False))) ∧ (False → True)) ∨ p1) ∧ ((p2 → p1) → False))) ∧ (True → p5)) → (p2 → p1)) := by
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
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h17 := h14 h16
      -- We need to get the right conjuct of h17 based on <expert-advice>.
      let h18 := h17.right
      -- We need to get the right conjuct of h18 based on <expert-advice>.
      let h19 := h18.right
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- One of the premise coincides with the conclusion.
      exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232291102099123684185957193483 : (((p2 → p5) → p4) → (p1 → ((((False → p1) ∨ (p4 → (((p1 ∧ (p3 → ((p1 → (False → p5)) ∧ p3))) ∧ p4) → p2))) ∧ p5) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116378880144332103329886672135 : ((((p1 → p2) → p1) → (p5 → ((((p3 → p3) ∨ (((False ∧ p3) → p5) → p5)) → (((p4 ∧ p1) ∨ p2) ∨ p1)) ∨ True))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706710187683756342545079709305 : (((((((True → p5) ∧ (p4 → p5)) ∧ p2) ∧ p5) ∨ ((True ∨ p5) → ((p3 ∨ p2) → (p1 ∧ ((p4 → (p4 → p1)) ∧ (p5 ∧ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775192266684671299666354195470 : (((False ∨ ((p3 → p2) ∨ ((p1 ∧ ((False ∧ (False → p2)) ∧ (p3 ∧ True))) ∧ ((False → (((True ∧ (p2 ∧ False)) ∨ p5) ∨ True)) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690239002997294739558424827574 : ((((p5 ∨ (p2 ∨ ((((p3 ∧ True) ∧ p3) → (p1 ∨ ((p4 ∧ p2) ∧ True))) ∧ p5))) ∨ (((p5 ∨ (p3 → p3)) ∨ p4) ∨ (p2 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41144568311946840700862168795 : ((((((p5 ∨ (p3 → ((p5 ∧ p2) ∧ True))) ∨ True) ∧ (p5 ∨ (((p2 → p3) ∨ (p4 ∨ p3)) ∨ p1))) ∨ ((p5 → p2) → True)) ∨ p3) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117151313724850579301369056178 : ((True ∧ ((True ∧ (((False ∨ p5) → False) → (p5 ∧ (((False ∨ (p4 ∨ True)) ∨ ((p5 → (False ∨ p2)) ∧ p4)) ∧ True)))) ∧ p5)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179120171729946723093507181268 : ((p1 ∧ (((((p3 → (True ∨ (p2 ∧ False))) ∨ p5) ∧ True) → p2) ∨ p1)) ∨ ((((p4 → (p4 ∧ True)) → p2) → (True → p1)) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133587100048252458292469310115 : ((((p3 ∧ ((((p2 → (p5 ∨ p5)) ∧ (((p5 ∨ p5) ∨ p3) ∧ (p3 ∨ (p5 → False)))) ∨ False) ∧ p2)) ∨ p2) ∧ False) ∨ (p4 → (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193035194681430422414166697225 : (((p3 ∧ ((p1 → (False ∨ p2)) ∨ p3)) → (True ∨ False)) → (((((((p2 ∨ p3) ∨ p1) → ((p5 ∧ p3) ∧ p1)) → False) ∨ True) → p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766160172981694988804406554119 : (((p4 ∧ ((p2 ∨ p5) ∧ (p2 ∧ ((p5 ∨ (p4 → (False ∧ (((p4 ∨ ((p3 ∧ True) → p5)) ∧ False) ∧ p5)))) ∨ ((p5 → p2) → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603202328791907652939920391197 : ((((p2 ∨ (((p3 ∨ (p2 ∨ ((True ∨ ((p3 ∧ True) → (True → False))) ∧ (False ∨ False)))) ∨ p3) → ((p5 → True) ∧ (False ∨ True)))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56185834749631516005074386535 : (((p4 ∧ ((True ∧ True) ∨ p4)) ∨ ((p4 ∨ ((((((True → p2) ∧ (((p4 → False) → False) → p5)) → p3) ∧ True) ∨ p2) ∧ p4)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111636881214718274326297214923 : (((((((((p5 ∧ (p5 ∨ True)) → p5) → p2) ∨ p2) ∨ p1) ∨ (((p1 → ((p5 ∨ False) ∨ p2)) ∨ p3) → False)) ∨ p4) ∨ False) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58602859307447912242204915600 : (((False → p1) ∧ ((p4 ∨ (p3 ∨ ((p2 → p4) → ((p3 ∨ p4) ∧ ((p4 ∧ ((False ∧ p4) ∨ p3)) ∨ (p3 → (p2 ∧ p5))))))) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_179647399318157811464643716252 : ((p5 → ((((p2 ∨ p1) ∧ (p5 ∧ p1)) ∧ ((False → p1) ∨ p5)) ∨ p1)) ∨ (((p2 → (False ∨ False)) ∨ (True ∨ False)) ∨ ((p3 → False) → True))) := by
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
theorem thm_5_vars_206255505617648216117102835512 : ((False ∨ (((p4 ∨ p5) ∨ True) → p5)) ∨ (((p3 ∨ (p4 ∨ p5)) → ((False ∨ p4) ∧ ((p2 → p5) ∧ p3))) → ((p5 ∨ p2) ∨ (p1 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309631443969455049241707176892 : (p2 ∨ (((p4 → (((False → (True ∧ p1)) ∧ p3) → p1)) ∧ (((True ∨ p3) ∧ ((True → (True ∧ p1)) → p1)) ∧ p3)) ∨ ((False ∨ True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214952479699414692334026962958 : (((p2 ∧ True) → (p1 ∧ p3)) ∨ (((((p4 ∨ (p4 ∧ ((p2 ∧ p2) ∨ (p2 → p5)))) ∧ p1) ∧ False) ∨ p5) ∨ (((False ∨ p2) ∨ True) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_215483103648550919183807141922 : ((p4 ∧ ((p2 ∧ p1) ∧ p5)) ∨ (p4 ∨ (p3 → ((((p3 ∨ (p5 ∨ (True ∧ p3))) → (p2 ∧ p3)) ∧ ((False ∧ True) → (p2 → p4))) ∨ p3)))) := by
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
theorem thm_5_vars_185212254377633261019822392700 : ((True ∧ (p5 ∨ (p4 ∧ ((p4 ∨ p1) ∨ ((p4 ∨ False) → p3))))) ∨ ((True → (p4 ∧ ((p1 → p2) ∨ False))) ∨ ((p3 ∨ p3) ∨ (False ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715406306019858349066447460645 : ((((((p4 ∨ p2) ∧ p1) ∧ p1) ∧ (((p3 ∨ (p5 → (p1 ∧ True))) ∧ ((True ∧ (p5 → p2)) → ((p1 ∨ (p1 → False)) ∧ p1))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56053448416250489154862763439 : (((((p3 ∧ p2) ∨ p1) → p3) ∨ (p5 ∨ ((p2 → p1) ∨ (p5 ∨ (((((p5 ∨ p5) ∨ (p1 → p2)) ∨ False) → p4) ∧ (True → True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66223271570009436482426408736 : ((p5 ∨ (((p5 ∧ ((p3 → p1) ∧ p1)) ∧ (False ∨ (p3 ∧ True))) ∨ ((p2 → p2) → (((False → p2) ∧ ((p4 → p2) ∧ p3)) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263367461316855896511341248253 : (True ∧ ((((((p2 ∨ ((p2 ∧ ((p2 ∧ ((p1 → p4) ∨ p2)) ∧ (False → False))) ∨ p1)) ∨ p5) → False) ∧ p4) ∧ False) ∨ ((p2 ∧ False) → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_320061770601833238966448047928 : (p4 ∨ ((p4 ∨ (p4 ∧ p1)) ∨ (p4 ∨ ((p2 ∨ (False → p4)) ∨ ((True ∧ p5) ∨ (p3 → ((p4 → ((p4 → True) ∧ (p2 ∧ False))) ∧ p4))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165009488492596995701723641397 : ((((False ∨ (p3 → ((p5 ∧ p3) ∨ p2))) ∨ (((p3 ∧ p4) ∨ p3) ∨ (p1 → p3))) → p1) ∨ (p3 → (p5 ∨ (False → (True → (p2 ∧ p3)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350984721580791124056963504798 : (p4 → (((p5 → False) ∨ (((((True → (((p4 ∧ p2) ∨ (False ∨ True)) ∧ (p4 → p3))) ∨ p5) ∨ p2) → p2) ∨ (p4 ∨ p4))) ∨ (p3 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191426209018513762882783610094 : (((p1 ∨ p5) → ((p3 ∧ ((p5 ∧ p1) ∨ p2)) ∨ p3)) ∨ (((((False ∨ True) ∧ (False → p1)) ∨ (p2 → False)) ∨ (p4 ∧ p1)) ∧ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_892371458129112964900654576764 : ((((((((((True ∨ (True ∨ p2)) → ((p3 → p1) ∧ False)) → (p2 ∧ p1)) ∧ p1) → p1) ∨ (True ∧ False)) → p1) ∧ (p1 → (p3 ∧ False))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p1 := by
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((((((True ∨ (True ∨ p2)) → ((p3 → p1) ∧ False)) → (p2 ∧ p1)) ∧ p1) → p1) ∨ (True ∧ False)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h4
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308401439638781596059964792894 : (p2 ∨ (((p4 ∨ ((((p2 ∨ p4) ∧ (p2 ∨ p2)) → (p3 ∨ (((p1 → True) ∨ False) → p2))) → ((True ∧ p2) → (p3 ∧ p3)))) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353669809164768853164012793685 : (p4 → (p5 ∨ (((p2 ∧ p1) ∨ (((p3 → ((p5 ∧ p5) ∨ (p1 ∨ (p1 ∧ False)))) → ((True ∨ False) → False)) → p5)) ∨ ((p3 → p3) ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157638281230045160761886950668 : (((p4 ∧ ((p3 → (p3 ∧ (p3 ∧ p1))) ∨ ((p2 ∧ (p4 → False)) ∧ False))) ∧ (p3 ∨ (p4 ∨ p5))) ∨ (p3 → (True ∨ (True ∨ (p4 ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136567568708854682054738119812 : ((((p5 ∧ p1) → False) ∨ ((((True → (p3 ∧ (p5 ∨ (((p3 → False) → True) → p5)))) → p5) → (False ∨ p2)) ∧ p2)) ∨ ((True ∨ p4) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110719053930804360511187856341 : ((((((p1 → p3) ∨ (((p5 → p2) ∧ ((p3 ∨ p2) ∧ ((p2 ∧ p4) ∧ p2))) → (p5 ∧ p2))) ∧ (p3 ∧ p1)) ∧ p1) ∧ p5) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



