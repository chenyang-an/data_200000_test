variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161823436889164460667732467614 : ((p5 ∨ (p4 → (((False → (p3 ∧ True)) ∨ p5) ∧ (((p3 ∨ p4) ∧ p4) → ((p1 → p4) ∧ p5))))) → (p5 ∨ ((p4 ∧ (p2 ∨ p1)) → p5))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h8 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h9 := h3 h8
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h11 : ((p3 ∨ p4) ∧ p4) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h12 := h10 h11
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h15 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h16 := h3 h15
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h18 : ((p3 ∨ p4) ∧ p4) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h19 := h17 h18
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- One of the premise coincides with the conclusion.
      exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301950958686482423359618775055 : (False ∨ ((p3 ∨ p3) → (((((p3 ∧ ((p4 → (p2 ∨ p1)) → ((p3 ∧ p5) ∧ (p5 ∧ False)))) ∨ (False ∧ True)) ∧ True) ∧ p3) ∨ (p2 ∨ p3)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666378004714743008585432535644 : (((((((False ∨ p1) ∨ ((False ∧ ((False ∧ (p4 ∨ p3)) ∧ p3)) → p1)) ∧ (p5 ∧ True)) ∨ (p2 ∧ (p2 ∨ True))) ∧ (p3 ∧ (True ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744185147086325407649246025763 : ((((p1 ∧ p1) → (((p3 ∨ True) ∨ ((p2 ∨ (False ∧ ((p3 ∨ p2) ∨ p3))) ∨ (p3 ∧ p1))) → (p5 ∧ ((p3 ∧ False) ∨ (p1 ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_439530711411625569207758555451 : (((((((p3 ∨ ((p2 → ((False ∨ (p1 → ((p2 → p2) → p3))) → p3)) ∨ False)) ∨ True) ∨ p3) ∧ (True ∨ p1)) ∧ ((p5 ∨ p3) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_201081906928973039100355206271 : ((p5 ∨ (p2 ∧ (p3 → (p5 ∧ (True ∨ p4))))) → (((False ∧ False) ∨ (True ∧ ((True → ((p3 ∧ False) ∨ (p5 ∨ p1))) ∧ p3))) ∨ (p1 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329211564536209118239668169081 : (True → (((True ∧ False) → p5) ∧ (False ∨ (((p5 ∧ p2) ∧ ((p1 → (((p4 → p3) ∧ (p2 ∨ p5)) ∨ (False → p1))) ∨ p2)) → (p5 ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  -- Conjunctions on the left can always be decomposed.
  let h12 := h5.left
  let h13 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h16 =>
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h17 =>
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187530818606735842989277868306 : ((p1 ∨ (False → ((p4 → (p4 ∨ (p5 ∧ True))) → (p3 ∧ p2)))) → ((p2 ∨ p5) → (True → ((((p4 ∨ True) → (False → p1)) → p1) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
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
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58617879893123681299203667437 : (((False → p3) ∧ (p1 ∨ ((p1 ∨ (False ∧ (p2 ∧ True))) ∨ ((((p5 → (((p4 → p4) → p1) ∨ p4)) ∨ (p5 ∧ p1)) ∨ False) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55331538483032110177094198484 : (((p4 ∨ (p1 ∧ ((False → p4) ∧ True))) ∨ ((p2 → p4) ∨ (p3 ∨ (True ∧ (((True ∨ p2) → p4) ∨ ((p3 → True) ∨ (False ∨ False))))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197056193282217606339099413689 : ((((p2 ∨ p4) ∨ ((True ∧ p2) ∧ p3)) ∨ p2) ∨ ((p5 ∧ ((p3 → p1) → p5)) → (p5 ∧ ((p5 ∧ True) → (p1 → (p5 → (p1 → p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h4.left
  let h9 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112790365241642081930064512531 : ((((p3 ∧ (False ∨ (p2 ∨ ((p5 ∧ False) ∨ p4)))) → (p1 → (p1 ∨ ((p2 ∨ (p5 ∨ (p1 ∧ p4))) → (p2 → p1))))) → p3) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634390550271395080121420925456 : (((((((((True ∧ p4) ∧ (p3 ∧ p4)) ∧ ((p4 → ((False ∧ True) ∨ p5)) ∧ p3)) ∨ (True ∨ p4)) ∨ p5) ∧ (p1 ∨ (p2 → p5))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60031526751281310284522584835 : (((p1 ∨ p3) → (((p4 ∧ p2) ∧ ((p3 ∧ (p4 → True)) ∨ (True ∨ (p4 → (False → (p5 ∧ (False ∧ (p4 ∧ (p3 ∧ p1))))))))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645967525628393451633134455541 : ((((True → ((((p3 ∨ (p1 ∨ ((p3 ∧ ((False → False) → p4)) → True))) ∨ p1) ∧ True) ∧ (p3 ∧ (p2 → (False ∧ (p5 ∧ p2)))))) → p3) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113500424700428456553702129305 : (((((p5 ∨ (False ∨ (p3 → p4))) → ((True ∧ ((p5 ∨ (False ∨ p3)) ∨ p1)) ∧ True)) → ((True ∧ p2) ∧ True)) ∨ (p1 ∨ p2)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_947396944438100437840232069368 : (((((p5 → (p4 ∨ p5)) → True) → ((p3 → ((p5 → ((False → (False ∧ (False ∧ p3))) → (False ∨ ((p3 ∨ p4) ∨ False)))) → p5)) ∧ False)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 → (p4 ∨ p5)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709925949435357445157709247115 : ((((((True ∧ (p3 → p5)) ∨ p3) ∧ p2) ∧ (((((p4 ∧ p3) ∨ (p4 ∨ (p5 ∧ p4))) ∧ (p5 ∨ True)) → ((p4 ∧ p5) ∧ p4)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748109185506928223140921867409 : ((((p1 → p3) → (((p2 ∨ (True ∧ p3)) → (((p4 ∧ p4) ∨ (True → (((p1 ∨ (p1 → (False → p4))) → False) ∧ True))) → p4)) ∨ p2)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h12 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h14 := h11 h13
      -- We need to get the left conjuct of h14 based on <expert-advice>.
      let h15 := h14.left
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h16 : (p1 ∨ (p1 → (False → p4))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- Implications on the right can always be decomposed.
        intro h18
        -- False on the left can always be used.
        apply False.elim h18
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h19 := h15 h16
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h23 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h24 := h11 h23
      -- We need to get the left conjuct of h24 based on <expert-advice>.
      let h25 := h24.left
      -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
      have h26 : (p1 ∨ (p1 → (False → p4))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h27
        -- Implications on the right can always be decomposed.
        intro h28
        -- False on the left can always be used.
        apply False.elim h28
      -- We have shown the premise of h25, we can now drive its conclusion.
      let h29 := h25 h26
      -- False on the left can always be used.
      apply False.elim h29
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112144025357268347751905256573 : (((p1 ∧ ((((p4 ∨ ((((p5 ∨ (True → p3)) → False) ∧ p1) ∧ (p5 → True))) → p2) → True) → ((p1 ∨ False) ∧ p1))) ∨ True) ∨ (p4 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143235512554020966320951537772 : ((p3 → ((p2 ∧ (((p4 → (p5 ∨ p4)) ∨ p1) ∧ (p2 ∨ ((((p4 → p3) → p4) ∧ (p5 ∨ True)) → p2)))) ∧ p2)) → ((p2 ∨ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653003861783285137252687296996 : ((((p5 ∨ (p2 ∧ (((p1 → p2) ∧ True) ∨ (((p2 ∨ p5) → p2) ∧ (p2 → (((False → p4) ∨ (p2 → p3)) → p5)))))) ∧ (True ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234145478747007292726202892091 : ((True → (True → p3)) → ((((p4 ∧ p4) ∨ ((((p4 ∧ ((p5 ∨ False) ∨ p5)) → p4) → (p5 ∧ True)) ∧ p2)) ∨ True) ∨ ((p5 → p5) ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671096929379309920722058631465 : ((((p1 ∨ (((True → (p1 → ((p4 → (True → (((False ∨ False) ∨ p4) ∧ (p3 → p5)))) ∨ p2))) → p5) ∨ p2)) ∨ ((p4 ∧ p1) → True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46562130201736587015333017696 : ((((False → True) → (((p5 → p2) ∧ ((False → p3) ∨ (p5 ∨ ((p3 → p1) ∧ (((p5 ∧ p3) → p5) ∨ True))))) ∨ p3)) ∧ (p3 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48330216872577335258595639565 : (((p1 ∨ (p2 ∨ ((True ∧ p4) → (((p1 ∨ False) ∨ (((False ∨ (p4 ∨ p1)) → p2) ∨ False)) ∧ ((p4 ∧ True) ∧ p2))))) → (p5 → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114166742064377755790940908834 : ((((True ∨ (p3 ∨ ((((p5 ∧ p4) ∧ ((False → (False → p4)) ∧ p4)) → p4) ∨ (p3 ∧ p5)))) → p1) → ((False → p2) → p3)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159201865849856920675275487712 : ((p2 → ((p5 ∧ (((((p3 ∨ True) ∧ p3) ∧ True) ∨ p4) → ((p5 ∨ p5) ∧ p2))) ∨ (False → p4))) ∨ ((p1 ∧ (p5 ∨ p5)) ∧ (True ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307406494289190262012538504048 : (p1 ∨ (p4 ∨ (False ∨ (False ∨ (p4 ∨ (p3 ∨ (((p5 → (False ∧ p3)) → True) ∨ ((False ∧ (p5 ∨ (p2 ∧ False))) ∧ (p3 → (p5 ∧ False)))))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184423905319613716740048307464 : (((((p2 → (False → p4)) → p4) ∨ (True → p4)) ∧ (p3 → p1)) ∨ (((True ∨ p1) → False) ∨ (True ∨ (((True → True) → (p3 → True)) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41325047243674002676518687757 : ((((p1 ∨ ((p4 ∧ ((p3 ∨ ((False → p4) ∨ (p2 ∨ (p4 → True)))) ∧ False)) ∨ p3)) ∧ (False ∧ (p4 → (p2 → (p2 → p2))))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757623041793986160074068627757 : (((p1 ∧ (p4 ∧ (((False → (p5 ∧ (p4 → p3))) → ((p3 ∧ p5) → ((p2 ∧ p5) → ((False ∧ ((True ∨ p1) → True)) ∨ p3)))) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115901830905214569624599220821 : ((((p2 ∧ (p3 ∨ False)) → p5) ∨ (p3 ∧ (p1 → (p2 ∨ (False ∨ ((p3 → ((True ∨ p4) → False)) ∨ (p5 → (p2 → True)))))))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320107792563833862929971519293 : (p4 ∨ (((p4 → p2) → False) → ((p4 ∨ p5) → (p3 → (((p3 ∨ False) ∧ (((True → (p4 ∨ p2)) → (p4 ∧ True)) → p1)) ∨ (False → p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193006517158774835912366575376 : ((((p3 ∨ (p2 → (p1 ∧ False))) → p4) → (p5 → p5)) → ((((True ∧ p1) ∧ p2) ∨ (True → ((p5 ∧ p2) ∧ p1))) ∨ (True ∨ (p4 ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152648756430196284151325561113 : (((True → p4) ∧ (True ∧ ((False ∧ False) ∨ (((p1 → (((p1 → p1) ∨ p4) ∧ True)) → (p3 ∧ p4)) → True)))) → (p5 → ((p1 → p2) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h11 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h13 := h4 h12
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64111021751568563932394825163 : ((False ∨ ((p1 ∧ ((False ∨ p3) ∨ (p4 ∨ (p5 → True)))) → (((p4 ∨ ((((True → p1) ∨ p2) ∧ p4) ∨ (p4 ∨ p4))) ∧ p3) ∨ p1))) ∨ p5) := by
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
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799576811544270148443641597626 : (((p1 → (p4 ∨ (((((p3 ∧ (p3 ∨ p5)) ∧ (p1 ∨ p5)) ∧ p4) ∧ True) → (((p1 ∧ p5) ∨ (True → ((p2 → False) ∨ p2))) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66453020371811140309552732625 : ((True → ((((p4 ∧ ((p3 → p3) → p4)) ∨ False) ∨ (p5 ∧ (False ∨ (((True ∨ True) ∨ True) ∨ ((p2 ∨ False) ∧ (p5 ∧ True)))))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611981672852423245466280021290 : ((((((((p5 ∨ True) → (p1 ∧ p3)) → (((True ∧ p5) ∨ ((((True ∨ True) ∨ p4) ∧ p4) → p4)) ∧ False)) ∨ p5) ∧ (p3 → p2)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_114151145919555251485116228122 : ((((((p1 → p1) ∧ (p3 → p4)) → (p3 ∧ (p4 ∨ (p1 ∧ (((False → p2) → p5) ∨ p3))))) ∨ p5) → ((p3 → p3) ∧ False)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593239780845940979490103606592 : (((((p5 ∧ ((False ∨ (p2 ∨ (((p5 ∧ (((p1 ∧ False) → p1) ∧ True)) ∧ p1) ∨ (p3 → p2)))) ∧ p2)) ∨ ((True ∨ p2) ∨ p4)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42610774847329914674329082074 : (((p3 ∨ ((p5 ∨ (((p4 → ((p2 → (((p1 → (p3 → p5)) ∨ False) → p3)) ∧ ((p1 → p1) ∧ p3))) ∨ p5) → p2)) ∨ p2)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159035755793076448584740303711 : ((p4 ∨ (p5 ∨ ((p4 ∨ ((p2 → (True ∧ (True → p4))) ∧ p3)) ∨ (((p2 ∨ p1) ∧ False) ∨ p2)))) ∨ (True ∨ ((p3 ∧ p4) ∨ (p3 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118337627357716156588140565177 : ((p2 ∨ ((((((False ∧ ((p2 ∨ (p5 ∧ (p4 → p4))) ∨ (p3 → (p2 ∨ False)))) ∧ p2) → p5) → (False → p5)) → False) ∨ p5)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167914205874814962362589268968 : (((p4 ∨ (p5 → (False → (p5 ∨ (p1 ∨ p2))))) ∧ (((True ∧ False) → p2) → (False ∧ p4))) → (((p3 ∧ False) ∨ (p5 ∧ (p5 ∨ False))) ∧ p5)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : ((True ∧ False) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h8
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h5
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h12 : ((True ∧ False) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- False on the left can always be used.
      apply False.elim h15
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h16 := h3 h12
    -- We need to get the left conjuct of h16 based on <expert-advice>.
    let h17 := h16.left
    -- False on the left can always be used.
    apply False.elim h17
  -- Conjunctions on the left can always be decomposed.
  let h18 := h1.left
  let h19 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h20 =>
    -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
    have h21 : ((True ∧ False) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h22
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- False on the left can always be used.
      apply False.elim h24
    -- We have shown the premise of h19, we can now drive its conclusion.
    let h25 := h19 h21
    -- We need to get the left conjuct of h25 based on <expert-advice>.
    let h26 := h25.left
    -- False on the left can always be used.
    apply False.elim h26
  case inr h27 =>
    -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
    have h28 : ((True ∧ False) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h29
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- False on the left can always be used.
      apply False.elim h31
    -- We have shown the premise of h19, we can now drive its conclusion.
    let h32 := h19 h28
    -- We need to get the left conjuct of h32 based on <expert-advice>.
    let h33 := h32.left
    -- False on the left can always be used.
    apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57290056601361117163243143761 : ((((p1 → p3) → p5) ∨ (((((False → (p3 ∨ p2)) ∨ (p4 ∨ p2)) ∧ (((p3 ∧ p4) ∧ (p2 ∧ p3)) ∨ p4)) → p1) → (False ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350220450769270167548812903448 : (p4 → (((False ∧ p3) ∨ ((p1 ∧ ((False → (p3 → (p3 → (p1 → (p1 ∨ False))))) ∧ (((True ∧ p4) → p3) ∧ (True ∨ True)))) ∨ p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149166447765766212585350794634 : (((p4 ∨ p2) ∧ (((((p2 ∨ True) ∨ p1) ∧ p3) ∨ (True ∨ (((p2 ∨ (p3 ∧ False)) ∧ True) → p3))) ∧ False)) ∨ (False ∨ (p1 → (False ∨ p1)))) := by
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
theorem thm_5_vars_739075445417625911633588929477 : ((((p3 ∧ p4) ∨ ((p4 ∧ True) ∧ (p3 ∨ (((p1 ∧ ((False ∧ (p1 → p4)) ∨ (True → p2))) ∧ (True → (p4 ∧ (False → p5)))) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149953876009869580970263169596 : ((p4 ∨ ((((p4 ∨ True) ∧ (((p3 ∧ p4) → p1) ∨ (p4 ∨ (p4 ∧ False)))) ∨ (p5 → (True ∧ p5))) ∧ p4)) ∨ (True ∧ ((p5 ∨ True) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786004578252747284689198731364 : (((p4 ∨ ((p4 ∨ ((False → (p4 → (p1 ∨ (False ∨ p1)))) → ((p3 → p1) ∨ (False → ((True ∨ (p5 → False)) ∨ p3))))) ∨ (False ∨ p2))) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136631912689917238251494254067 : ((((p1 ∨ p4) ∨ p1) → ((True → ((((((True → p2) ∨ (p5 → p4)) ∧ True) ∨ True) ∨ p5) → p4)) ∧ (False ∧ p1))) ∨ ((p5 ∧ False) → p5)) := by
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
theorem thm_5_vars_47050552515183928832678354179 : ((((p4 ∨ ((p4 ∧ p3) ∧ (p2 → ((((p2 ∧ p5) → (p2 → (False ∧ p3))) ∨ (True ∧ True)) → p2)))) ∧ (False ∨ p5)) ∨ (False → p4)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111328912790907209238438501150 : (((p2 ∧ (((p3 ∨ False) ∧ (p3 ∧ (True ∨ (True ∨ ((p4 → p1) ∧ (p5 ∧ p5)))))) → ((p1 ∧ True) → (p2 → p5)))) ∧ p1) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801650292632218625798771878218 : (((p2 → (((p5 → p1) ∧ (True ∧ False)) ∨ (((p4 → ((p3 → True) → (p5 ∨ True))) ∧ (p1 ∨ p1)) → (((p5 ∨ False) ∧ p5) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117715034220070574828616715423 : ((p3 ∧ (p1 ∨ ((((p5 ∧ True) ∧ (False ∨ ((True → ((p2 ∧ False) → p5)) ∧ (p1 → ((True → p4) ∨ False))))) → p1) ∨ p4))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677541521201932003687831150131 : (((((False ∨ (((((p1 → ((p1 ∨ (p2 ∨ False)) ∨ (p1 ∧ p3))) ∨ p4) → True) → p5) ∧ True)) ∨ True) ∨ (((False ∧ p5) ∨ p2) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164824938191816236246630750986 : ((((p2 ∨ p5) → ((((p3 ∨ ((True ∧ p2) → p4)) ∨ (p3 ∨ p4)) ∨ p1) → p1)) ∨ True) ∨ ((((p2 → p3) ∧ p4) ∨ p1) → (p5 ∧ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165164680272447171680236544406 : ((((p4 → False) ∧ ((False → (p3 ∨ (p1 ∧ (p1 → (p1 → False))))) ∨ p1)) ∧ (True ∨ p5)) ∨ (((p5 → ((p4 → p5) ∨ p2)) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205117426052338110904577821074 : ((((p4 ∨ p2) ∨ False) ∧ (False ∧ p2)) ∨ ((((p2 ∧ False) ∧ p3) → True) ∧ ((True ∨ p4) ∧ (((True ∨ p5) ∨ (p4 ∨ (False ∨ True))) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53554812984215509460581959494 : ((((p2 → ((False ∨ p5) ∨ (p4 → (p4 ∨ p1)))) ∧ p5) ∧ (p3 ∨ (((True ∨ (p1 ∨ True)) ∧ ((p2 → p1) → (p2 ∨ p2))) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136189243375084281951053184266 : (((((p2 ∨ False) → p4) → (p3 ∨ False)) ∧ (p5 ∨ (((False → (False ∨ (p2 ∨ (p2 → p5)))) → (p2 → p1)) ∨ False))) ∨ ((p4 ∧ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198993814189236975076930663321 : ((p5 → (p3 ∨ (p3 ∨ ((p3 → True) → False)))) ∨ ((p1 ∧ ((((False ∧ True) ∨ p1) ∨ ((p2 → False) ∨ False)) ∧ (True ∧ (p2 ∧ True)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740761586557046067135320183223 : ((((p2 ∨ p5) ∨ (((p4 ∧ ((p5 → False) ∨ False)) ∨ (((p2 ∨ False) ∧ True) ∧ p1)) → (p2 ∧ (p1 ∨ (((p2 → False) ∨ True) → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182118689380565025473585539341 : (((True → ((((p2 ∧ (p5 → p4)) → p2) → p1) → False)) ∨ True) ∧ (False ∨ ((p5 ∨ False) → ((p1 → (p2 ∨ p1)) ∨ ((p2 ∨ p1) → p1))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46352019602258431846674685425 : ((((((p1 ∧ (p2 ∧ (p3 → ((True ∧ False) ∧ p4)))) ∧ p3) → (True → True)) → ((p1 ∨ (p5 → p5)) ∧ (True → False))) ∧ (p4 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141894961814758645530238072347 : (((p3 → p3) ∨ ((p5 ∧ (p1 ∨ ((p2 ∨ p2) ∨ (True → False)))) ∨ (p4 ∧ (((p1 ∨ True) ∧ p2) ∧ (p4 → p4))))) → ((False ∨ True) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
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
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h16.left
      let h19 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214707365975783111719773479813 : (((False ∧ p4) ∨ (p1 ∨ p1)) ∨ ((p3 ∧ (((p2 ∧ (p2 → p4)) ∨ p1) → (p5 → p2))) ∨ ((p4 ∧ ((p1 → p1) → (False → p3))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123553612717000354762999993364 : ((((((True → (p4 → p5)) ∨ ((True ∨ p2) → ((p5 ∧ True) ∧ p3))) ∧ True) ∨ False) ∨ (((p5 ∨ (False ∧ p2)) ∧ False) → p1)) → (p5 ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
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
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147959048106667977477540705369 : (((False ∨ ((True ∨ (((p4 ∧ p1) → (p3 → (p5 → (p3 ∨ p5)))) → (p2 → p5))) → p1)) ∧ (True ∨ False)) ∨ (p3 → (True → (p4 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206410631692300588481468322336 : ((p3 ∨ (False ∧ ((p2 ∧ p4) ∨ p2))) ∨ ((False → (p3 → (p1 ∧ (p5 → ((False ∨ (True ∧ ((p3 ∨ True) ∨ True))) ∨ p5))))) ∨ (p4 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56929347660722067961530972998 : (((True ∨ (p2 → p3)) ∧ ((p5 → (((p3 ∧ ((True ∨ (True → (p4 → ((p4 ∨ (False ∧ p3)) ∨ p2)))) → p5)) → p3) ∨ p4)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114323629544780745582702689226 : ((((True ∧ p4) ∨ ((p3 ∨ (True ∧ p2)) → (((True ∨ False) ∨ (p3 → (p3 → True))) → p4))) ∧ ((p5 → (p1 → p2)) ∨ p5)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40173091766015876654418760937 : ((((((p3 ∧ True) ∧ ((True ∨ False) ∨ False)) ∨ (p4 → (p4 ∧ (((False ∨ (p3 ∨ p2)) ∨ (p3 ∨ (True → p4))) ∨ True)))) ∧ True) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178451561883051389732427132097 : ((((True ∧ p5) ∨ (p3 ∨ (False ∨ (p1 ∧ p1)))) ∧ (p4 ∧ (True → p4))) ∨ ((p5 ∨ ((p3 ∧ False) → ((False ∧ p4) ∧ p5))) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241536129027980845738071770908 : ((False → p3) ∧ (((((p4 ∨ (p1 → p2)) → (p3 → (False ∨ False))) ∧ (True ∨ (True ∨ p4))) ∨ p4) ∨ ((p2 → ((p4 ∧ p4) ∨ True)) ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315658087597014473063451020560 : (p3 ∨ ((p2 ∧ p4) ∨ ((p5 ∨ (p1 ∨ False)) ∨ (((p3 ∧ (((True ∨ False) ∧ (True ∨ p4)) ∨ p5)) ∨ ((p5 → (p4 → p3)) ∧ p3)) ∨ True)))) := by
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
theorem thm_5_vars_65638306833535730935009340575 : ((p4 ∨ ((((p4 → (((p4 ∨ ((p4 ∧ p2) ∨ p5)) ∧ p2) ∨ (False ∨ p1))) → p4) ∨ (True → (p4 → (p5 → (p4 ∨ p2))))) ∨ p3)) ∨ p1) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41650404991625236132813474568 : (((((p5 ∧ (p3 → p4)) ∨ (p2 ∧ p2)) ∧ (((False ∧ False) ∨ (((p4 ∧ True) ∧ False) ∧ (p5 ∨ (p3 → p4)))) ∨ (p5 → False))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161141006139578870346059584236 : (((p3 → p3) ∧ ((False ∧ (p2 ∧ True)) → ((p5 ∧ p3) ∧ ((p1 → (False ∧ p1)) ∧ (True ∧ p4))))) → (((True → False) → p5) ∧ (True ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319456408562034485034469302043 : (p4 ∨ ((((((p5 → p1) ∨ False) → p3) → (p3 → p2)) → (p2 → False)) ∨ ((True ∧ False) → (p1 → ((True ∨ (False → p4)) ∨ (True → False)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317844277941513528274677943965 : (p4 ∨ (((True ∧ (p3 → p2)) → (p3 ∧ ((True ∧ (True → ((p3 ∨ (p1 → p1)) ∨ (False ∨ (p3 ∧ True))))) ∨ ((False → p5) ∨ p4)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197702391458371747523055886084 : (((p1 → (p4 ∧ (False → p5))) → (p4 ∧ p2)) ∨ ((p2 ∧ (p5 ∨ (p3 ∨ p5))) → (((True → p4) → ((p5 ∨ (p4 ∨ p5)) → True)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261455545169710551850049971111 : ((p5 → p2) → (((p4 → (((p1 ∧ p4) ∨ (p1 → p5)) → (((False ∧ p2) ∧ p3) → p4))) → p1) ∨ (p4 ∨ ((p4 ∨ (p1 ∨ True)) ∨ True)))) := by
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
theorem thm_5_vars_739672223956921442846034173427 : ((((p5 ∧ p5) ∨ (p5 ∧ ((p1 ∨ p4) ∧ (((p5 → ((False ∧ p3) → False)) ∧ (((p1 → False) → False) ∧ True)) ∨ (p2 ∧ (p2 ∧ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162064777037525303211492020792 : ((p5 → ((p2 ∨ ((p4 ∨ (p1 ∧ ((p3 ∧ False) ∨ p2))) ∧ p2)) ∧ (((p5 ∧ True) → False) ∨ True))) → ((True → p1) ∨ ((p2 → p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147454932974339650188187429062 : ((((p4 ∧ p3) → (p3 ∧ (p1 ∨ (p1 ∨ (((p2 → False) → False) ∧ ((True ∧ (p5 ∨ True)) ∧ True)))))) ∨ True) ∨ (p3 → ((True ∧ True) ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344755642326339156405017892378 : (p2 → (p3 → (p1 ∨ ((p2 ∧ (p1 ∧ ((p4 ∧ (((True → False) ∧ ((False ∧ ((True ∨ p2) ∨ False)) ∨ True)) ∧ p1)) ∨ False))) ∨ (True ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54452861814399286789530615209 : (((((p2 → (p2 → True)) ∨ (p5 ∨ False)) → p2) ∨ ((((p1 → (p4 ∧ p4)) ∧ (p1 ∨ False)) ∨ (((p4 ∧ p4) → p3) ∧ p4)) → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51626217568588526009421375303 : ((((p1 ∨ (((p1 ∨ ((p4 → p5) ∧ True)) → (p5 → (p2 ∧ p1))) ∨ p1)) ∧ True) ∧ ((False → True) ∨ ((False ∨ (False → p1)) → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52325938541196181202505910746 : ((((p2 ∧ ((p3 ∨ (p2 ∧ (True ∨ (p5 ∨ p5)))) → (p3 ∧ p3))) ∨ False) ∧ ((p2 → (p5 ∨ (p1 ∧ (True ∧ True)))) ∨ (p2 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756920732784453862873114087291 : (((p1 ∧ (((p3 → ((p4 → p1) → p5)) ∧ p5) ∨ ((((p3 ∧ p3) → p5) ∧ p3) ∨ ((((p3 ∨ True) → False) ∧ (p5 ∧ True)) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336106964043934611160660966668 : (p1 → (((((p1 ∧ ((p2 ∨ p3) ∧ False)) ∨ ((p2 ∨ (((p4 ∨ True) → (True ∧ ((p3 → p5) → p1))) ∧ False)) ∧ p5)) ∧ p5) ∨ p5) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40888419829255339863521390650 : (((((((p3 ∨ p3) → (p2 ∧ (False ∨ p5))) → p4) → ((True ∧ ((p1 ∧ True) ∨ ((p4 → p4) ∧ p1))) ∨ False)) ∧ (True ∧ True)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67571161618663566875140087140 : ((p1 → ((False ∨ p2) ∨ ((p4 ∧ (p5 → False)) ∧ (((False ∧ True) → ((p1 ∨ ((p4 ∧ p1) → (p5 ∧ p1))) ∨ p5)) ∧ (p2 → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695970861403763338429424237024 : ((((True ∧ ((p4 → (p2 → p1)) → (p1 → (((p3 ∨ p4) ∨ p1) → p3)))) → ((((False → (True ∧ p5)) → p5) ∧ p3) ∧ (p4 ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655845457247185840844160639121 : ((((((((p4 → True) → ((True ∧ False) ∧ (p4 ∨ (p2 ∧ False)))) ∨ (True ∨ False)) → (p2 ∧ p5)) → ((p5 ∧ True) ∧ True)) ∨ (p5 ∨ p2)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 → True) → ((True ∧ False) ∧ (p4 ∨ (p2 ∧ False)))) ∨ (True ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141716828918929838509329612596 : (((p3 ∨ True) ∧ ((p5 ∧ (p5 ∧ ((p2 ∧ ((((True → p4) ∧ (p4 ∨ p1)) ∧ True) ∨ p4)) ∨ True))) ∨ (p4 ∨ p2))) → (False ∨ (p5 ∨ True))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
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
          cases h17
          case inl h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h8
          case inr h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h8
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h8
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h31.left
        let h33 := h31.right
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- Conjunctions on the left can always be decomposed.
          let h35 := h34.left
          let h36 := h34.right
          -- Conjunctions on the left can always be decomposed.
          let h37 := h35.left
          let h38 := h35.right
          -- Disjunctions on the left can always be decomposed.
          cases h38
          case inl h39 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h29
          case inr h40 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h29
        case inr h41 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h29
      case inr h42 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h29
    case inr h43 =>
      -- Disjunctions on the left can always be decomposed.
      cases h43
      case inl h44 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h45 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197888620155918095621142627192 : ((((p5 ∧ p4) → p3) → (p3 ∧ (p1 ∧ p1))) ∨ ((p1 ∨ p3) ∨ (p1 ∨ (p2 ∨ (True ∨ (p1 → (p2 → (True ∨ ((p2 ∨ p2) ∧ False))))))))) := by
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



