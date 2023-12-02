variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53510344364855100630767758360 : (((p5 ∨ ((p5 ∨ ((True ∨ ((p3 ∨ False) ∨ p2)) ∧ p1)) ∨ p4)) → ((((p5 ∧ p5) ∨ p2) → (True ∧ p1)) ∨ ((p1 ∨ True) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165480890976836575284829421544 : ((((((p4 → (p2 ∨ False)) → (False ∧ p5)) ∨ p2) → p3) ∨ ((p5 → p3) ∨ (p3 → p1))) ∨ (((True ∨ (p3 → (True → p5))) ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48152817730742070716437172035 : ((((p1 ∨ (p2 → p5)) → ((p3 ∨ ((((p1 → p2) ∨ p1) ∧ p4) ∧ True)) → ((p5 ∨ p1) ∧ ((p2 ∨ p1) → p5)))) → (True → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684682343123185347368196636532 : ((((((p4 ∨ p5) → p4) → (((True ∧ (((p2 ∧ True) ∧ (p4 ∨ p3)) → p4)) ∧ p1) → False)) ∨ (False ∧ (((False ∧ p1) ∨ p5) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302831928279988275270612161548 : (False ∨ (p5 ∨ ((True ∧ (p4 → p4)) → (((p1 ∧ p5) ∧ (p4 ∨ (((((p3 → p4) ∧ p5) → True) ∨ False) ∧ True))) ∨ (True ∨ (p1 ∧ False)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32846746345890608225015047371 : ((p3 ∨ ((((p2 → ((((True ∨ p2) → False) → (True ∧ p3)) ∧ p2)) ∧ ((p2 ∧ (p2 ∨ p4)) ∧ (False → p4))) ∨ (True → True)) ∨ True)) ∧ True) := by
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
theorem thm_5_vars_114519544191492724000113747828 : (((p1 ∧ (p4 → (((p2 ∨ (True ∧ ((True → p1) ∧ p2))) → (p4 ∧ (p3 ∨ p5))) ∧ p4))) → (p5 ∧ (True ∧ (True → p2)))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67485272103225834296534211501 : ((p1 → ((((((p5 ∨ True) → ((p3 → p2) → p3)) ∨ p5) ∧ p2) ∧ True) ∧ (True → (True → (((p4 ∨ False) ∧ (p5 ∨ True)) → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198066504923859533686544236210 : (((False ∨ p3) ∨ (p2 ∨ ((p1 ∨ p1) → False))) ∨ (((((True → (p2 ∨ (p2 ∧ p3))) → p5) → False) ∨ (True ∨ False)) ∨ ((p3 → p2) ∧ p2))) := by
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
theorem thm_5_vars_800438314248964028620410272950 : (((p2 → ((True → ((p1 ∨ (p2 ∧ ((p5 → ((p4 ∧ True) ∨ True)) → (p1 → p1)))) → ((p4 ∨ p4) ∧ ((False ∨ p5) ∧ False)))) ∨ p2)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228572287997597306062199924738 : ((p1 ∨ (p2 ∨ p2)) ∨ ((((True → False) → (False ∧ (p4 → False))) → p1) → ((((p5 → p2) → (p3 ∧ (p2 → (p5 → p1)))) ∨ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172828409577644635620393562951 : ((True ∧ (p5 ∧ (p1 ∨ ((p2 ∧ (p3 → False)) ∨ ((False ∧ True) ∨ (p2 ∧ p1)))))) ∨ ((p4 → ((((p3 → True) → p1) → p4) ∨ False)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172708306996691833167111125234 : (((p1 ∨ p5) ∨ ((True ∧ p4) ∨ ((True → (p4 → (p2 ∨ (True ∨ p4)))) ∧ p5))) ∨ (True → (((False ∧ (False → False)) ∨ (p1 ∨ p3)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308457495219517102956487193347 : (p2 ∨ (((((((((((p5 ∨ True) → p3) → True) ∧ p1) → False) → p1) ∧ (((False → p3) → p1) ∨ False)) ∨ False) ∨ True) ∨ (p2 ∧ p4)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713567603296959473468394135910 : ((((((p4 ∨ (p3 ∧ True)) ∧ p1) ∧ p4) → ((p3 ∧ True) ∨ ((p3 → ((p1 → p1) → (False ∨ (p4 → p5)))) ∧ (p2 ∧ (p1 ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157681896303959549008636701410 : (((p3 ∧ ((((True ∨ True) ∧ ((p5 → p3) → p5)) ∨ (p3 ∧ p3)) ∧ p2)) ∨ (True → (True ∨ p2))) ∨ ((((True ∨ p3) → True) ∧ p5) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258654245951455178956731806991 : ((p5 ∨ p5) → ((((False → p5) ∨ (((p4 ∧ True) ∨ (p1 ∨ (p5 ∨ (True → p1)))) ∧ False)) ∧ (((p3 ∨ False) ∧ p4) ∨ p5)) ∨ (False ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178810658235209401462882828269 : (((False ∧ (p3 → p4)) ∨ ((p3 → (((p5 ∨ p1) ∨ False) ∧ p3)) ∨ p2)) ∨ (((((p4 ∨ (p4 ∨ False)) ∧ (p1 ∧ p4)) → True) ∨ p3) ∨ p2)) := by
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
theorem thm_5_vars_249560824245565777793220258992 : ((p5 ∨ p2) ∨ ((False → (p3 ∨ (False ∧ p5))) ∧ (p1 ∨ ((((((p1 ∨ p5) → p2) ∨ p1) → p4) ∨ ((p2 → p2) ∨ p1)) ∧ (p4 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735428712117656685150465077915 : ((((p4 ∨ p3) ∧ ((((((((False ∨ p1) ∨ (True ∨ p3)) → (p3 ∨ p3)) ∨ (p5 ∧ ((p1 → p2) ∨ p2))) ∧ p4) ∨ False) ∧ True) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133713060754700932162698272204 : (((((((False ∨ p2) ∨ p1) ∧ p3) ∧ (p2 ∧ ((p2 ∧ (p2 ∨ p4)) ∨ p1))) → ((p1 ∨ p1) ∧ (p4 ∨ p4))) ∧ True) ∨ ((p3 → p3) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171956289843012474091257882548 : (((((p3 ∨ p3) → True) ∧ (True ∨ ((p2 ∧ (True → p1)) ∧ False))) ∧ (p5 ∧ p2)) ∨ ((p1 → ((((p5 ∨ p5) ∨ p5) ∨ True) ∨ False)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43536898445870624887916111582 : ((((p2 → (p1 ∨ ((p4 ∧ (((p3 ∧ ((p4 → p3) → (False ∧ p5))) → (True ∨ (p1 ∧ False))) ∧ p4)) ∨ (p3 ∧ p4)))) ∨ p5) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164722394122161425966173015997 : (((((((p3 ∧ p4) → (p5 ∨ p3)) ∧ p3) ∧ (((p4 → p4) → p4) → True)) → p1) ∨ p2) ∨ ((p4 ∧ False) → (p2 → ((p4 ∨ p5) ∨ p3)))) := by
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
theorem thm_5_vars_608996837606243144321686743362 : ((((((p2 ∧ (p5 ∧ (p3 → (p2 ∧ (p3 ∧ (False ∨ p1)))))) ∧ (((True ∨ p4) ∨ False) → (p1 ∧ ((p1 ∨ p1) ∨ p3)))) ∨ True) ∨ p1) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_190446862684191115085094457068 : (((p2 → ((p3 ∨ (p3 → (p5 → True))) → p5)) ∨ False) ∨ (((p1 ∨ (p5 → ((p5 ∨ (False ∧ p3)) ∧ p3))) → ((p3 → p5) ∧ p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169032100705767605620061835479 : ((p2 → (((p5 ∧ ((p1 ∨ p3) → p4)) ∧ (p1 ∧ ((True ∨ p3) ∨ p5))) → (p1 → False))) → ((p2 → (p5 ∧ (p5 ∨ p3))) ∨ (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130094845155948026722909566337 : ((((((((p4 ∧ (p3 ∨ p4)) → (p4 ∨ (p1 → p4))) ∨ ((p1 ∧ p1) ∧ p4)) ∧ p4) ∧ p5) → False) ∨ (False → p2)) ∧ ((p2 → p2) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139225667574689555533773373096 : ((((p4 ∨ (True ∨ p3)) → (((p3 → (p4 ∨ ((p4 ∨ True) ∨ ((p5 ∨ p1) ∧ False)))) ∧ (True ∧ True)) ∧ p3)) ∨ p3) → ((False ∨ p2) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (p4 ∨ (True ∨ p3)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- We need to get the right conjuct of h4 based on <expert-advice>.
    let h5 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160709182332759749500703704323 : (((((p3 → (p3 → p2)) → True) ∨ (p1 ∧ p1)) ∨ (((p1 → ((p1 ∨ False) ∧ p5)) ∨ p3) ∨ p5)) → (((p4 → (p5 → p3)) → p1) ∨ True)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
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
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135177392507360587665135418212 : (((((p1 → (p4 → ((((p3 ∧ (True → p5)) → p4) → (p1 ∨ False)) ∧ p3))) → (p1 ∧ p3)) ∨ True) → (p2 ∧ p5)) ∨ (False → (p1 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46672009239170416402339478188 : (((p1 ∨ ((p3 ∧ (True → ((p5 ∨ (((True → True) → p3) ∨ (False → (True ∧ p4)))) ∧ True))) → ((False → p2) ∧ False))) ∧ (p5 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41609269042218326797103309357 : (((((p3 ∨ True) → ((p5 ∧ p3) ∧ (p5 → p1))) ∨ (p4 ∧ (p3 → ((p2 ∨ p5) ∨ ((p5 ∨ p3) ∧ (p4 ∨ (p1 → p5))))))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58167737948682891242846806205 : (((p3 ∧ False) ∧ (p4 ∧ ((p1 ∨ p1) ∨ ((p4 ∧ False) ∧ ((((((p1 ∨ (p1 ∨ (True → p5))) ∨ p4) ∧ True) ∧ True) → p4) → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61883039251562385711477953414 : ((p2 ∧ ((p3 ∨ ((False ∨ p1) → ((p5 ∧ (p2 → p2)) ∧ (p4 ∧ (p5 → ((((p1 → p1) ∨ p3) → p4) ∨ p5)))))) ∧ (True ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678011626812763790483356194999 : ((((((True ∧ p2) ∨ ((True ∧ ((False → (p5 ∧ False)) → (p4 ∧ p4))) ∨ False)) ∧ ((p5 ∨ True) ∧ p4)) ∨ (((p2 → True) ∨ p4) → True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_606220914725643741947918298524 : (((((((False ∨ ((False → True) → p2)) → ((False ∨ (True ∨ ((p3 ∨ p4) ∨ ((False ∨ p2) ∨ (p3 ∧ p3))))) → p1)) ∧ p4) ∧ p3) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148368648479702801515496886933 : (((((True ∧ ((((p4 → p4) ∧ (False ∧ True)) ∧ p2) ∧ False)) ∧ True) ∨ p1) ∨ (p2 ∧ ((False ∧ p4) ∨ p4))) ∨ (True ∨ ((p4 ∨ p4) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303807278266405084395693785400 : (p1 ∨ ((((p3 ∧ (True ∧ p4)) ∨ (p4 ∨ (((p3 ∧ True) ∨ ((p4 ∨ (p4 → True)) → (p2 ∨ p4))) ∧ (p2 → (p4 ∧ p4))))) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224425323797427326898079495922 : ((p1 → (False ∨ True)) ∧ (((True ∨ (p5 ∧ (((p1 → p1) ∧ (False ∧ (p5 ∨ False))) ∨ p2))) → (p5 ∨ (p3 ∧ (p5 ∨ (True ∧ False))))) ∨ True)) := by
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
theorem thm_5_vars_57230428769022070446492121178 : ((((True ∧ p2) → p1) ∨ (((False → ((p2 ∨ p3) ∨ ((((p4 ∨ True) → p4) ∨ p4) ∧ (p4 ∨ p3)))) → (True → (p2 ∨ p5))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176982323098153307545794701411 : (((p3 ∨ p3) → (p1 ∨ ((True → ((p2 ∧ (True ∨ p1)) ∨ False)) ∨ True))) ∧ (((((p2 ∨ (False → p4)) ∨ p1) ∧ p1) → True) ∨ (False → False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733680817298645285548114136025 : ((((p5 ∧ False) ∧ ((p3 → ((p1 ∨ p4) ∧ p2)) → ((((True → False) ∨ (((True ∨ (p1 → p3)) → p2) → True)) ∧ p1) ∧ (p2 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687868697076466519773948705350 : ((((((False → (p4 ∨ (p3 ∧ p3))) → ((p1 → True) ∧ False)) ∨ ((p5 → p3) ∧ p2)) ∧ (((p1 ∧ p1) ∧ p4) ∨ ((p4 ∧ False) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127980267919144703570789486300 : ((p1 → ((p1 ∨ (((p2 → p3) ∨ (((True → p4) ∨ p4) ∧ (False → (p3 → (False ∧ p4))))) ∨ (p1 ∧ (p4 ∧ p1)))) ∨ p3)) → (p3 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191389337694278099990790883423 : (((p5 → p3) ∨ ((p2 → p3) → (p4 ∨ (True → False)))) ∨ ((True ∨ p4) → ((((p5 → True) → (p2 ∧ p3)) ∧ p5) → ((p1 ∧ p3) ∨ p2)))) := by
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
  cases h1
  case inl h5 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : (p5 → True) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h6
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : (p5 → True) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h11
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266243260656441473429184156268 : (True ∧ (p5 → (((p4 ∨ p1) ∧ (p5 ∧ ((p4 → (((p3 → (p3 ∧ ((p2 ∧ p3) ∧ False))) ∧ (p3 ∨ False)) → (p2 ∨ False))) → False))) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52168119031783430879060297401 : ((((((p3 → p3) → ((p4 ∧ p1) → True)) ∧ True) → (True → ((False ∧ True) ∧ p4))) → ((p1 ∧ (p1 ∨ False)) ∧ (False ∧ (True → False)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 → p3) → ((p4 ∧ p1) → True)) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : (((p3 → p3) → ((p4 ∧ p1) → True)) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h10
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h14 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h15 := h13 h14
  -- We need to get the left conjuct of h15 based on <expert-advice>.
  let h16 := h15.left
  -- We need to get the left conjuct of h16 based on <expert-advice>.
  let h17 := h16.left
  -- False on the left can always be used.
  apply False.elim h17
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h18 : (((p3 → p3) → ((p4 ∧ p1) → True)) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h19
    -- Implications on the right can always be decomposed.
    intro h20
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h21 := h1 h18
  -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
  have h22 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h21, we can now drive its conclusion.
  let h23 := h21 h22
  -- We need to get the left conjuct of h23 based on <expert-advice>.
  let h24 := h23.left
  -- We need to get the left conjuct of h24 based on <expert-advice>.
  let h25 := h24.left
  -- False on the left can always be used.
  apply False.elim h25
  -- Implications on the right can always be decomposed.
  intro h26
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h27 : (((p3 → p3) → ((p4 ∧ p1) → True)) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h28
    -- Implications on the right can always be decomposed.
    intro h29
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h30 := h1 h27
  -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
  have h31 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h30, we can now drive its conclusion.
  let h32 := h30 h31
  -- We need to get the left conjuct of h32 based on <expert-advice>.
  let h33 := h32.left
  -- We need to get the left conjuct of h33 based on <expert-advice>.
  let h34 := h33.left
  -- False on the left can always be used.
  apply False.elim h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249072982987256442169503969342 : ((p4 ∨ p1) ∨ (((p5 ∨ (True ∨ (p5 → p4))) ∨ p4) ∧ (p1 ∨ (p4 ∨ ((p5 → ((p4 → (p5 ∨ (p5 ∨ True))) → False)) → (True ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_746245162321450753068630634384 : ((((p1 ∨ p4) → (p4 ∧ (True ∧ ((p5 → ((True ∧ p3) ∧ (p3 ∧ ((p2 ∨ (p2 ∧ (p4 ∧ p4))) ∧ ((p3 ∨ p5) ∧ p3))))) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655335281747524586709576617913 : ((((((((p1 ∨ (p1 ∧ ((False ∨ ((False → p5) → p4)) → p3))) ∧ ((False ∧ p1) ∨ True)) ∧ p4) ∧ p2) ∨ (p4 ∨ False)) ∨ (False ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767920074790472945119521727894 : (((p5 ∧ (((p5 → p5) ∨ (((False → ((((p4 → False) ∧ ((p3 → False) ∧ (p3 → (p2 ∧ p5)))) → p2) → p4)) → p1) → p4)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319210663916340420770463134490 : (p4 ∨ (((((p4 ∧ p2) → (True ∧ False)) ∧ p5) → (((p2 → (True → True)) ∧ (p2 ∧ True)) → False)) → ((False ∨ (p3 ∧ (p4 → p3))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187218134071325881821263822399 : (((p1 → False) → ((p1 ∧ p5) → ((p2 ∧ (p5 → False)) → p1))) → ((p1 ∧ p3) → ((p5 ∨ (((True → (p1 ∨ p4)) → False) ∨ p1)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232876208500477989449977836429 : ((p2 ∧ (p4 → p5)) → ((((((((p1 ∨ p2) ∨ p5) ∧ (((p3 ∧ p1) → p3) → (p5 ∨ False))) ∨ p2) ∨ p2) → p2) → p5) ∨ (p2 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605598224813269264688682421137 : ((((p4 → ((((p3 → ((p2 ∧ p2) → p5)) → (p1 → (p2 → ((p1 ∨ (p4 ∧ (p4 ∧ p5))) → False)))) ∨ (True ∨ True)) ∨ p1)) ∧ True) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84021908762628930130224567295 : ((((((p1 ∨ (((p1 → p2) → p3) ∧ p4)) ∨ (p5 → p1)) → (True → p1)) → p5) ∧ ((((p1 → p5) → p4) → p4) → (p4 ∧ False))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p1 → p5) → p4) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (p1 → p5) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : (((p1 ∨ (((p1 → p2) → p3) ∧ p4)) ∨ (p5 → p1)) → (True → p1)) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- Implications on the right can always be decomposed.
        intro h10
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- One of the premise coincides with the conclusion.
            exact h12
          case inr h13 =>
            -- Conjunctions on the left can always be decomposed.
            let h14 := h13.left
            let h15 := h13.right
            -- One of the premise coincides with the conclusion.
            exact h7
        case inr h16 =>
          -- One of the premise coincides with the conclusion.
          exact h7
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h17 := h2 h8
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h18 := h5 h6
    -- One of the premise coincides with the conclusion.
    exact h18
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h19 := h3 h4
  -- We need to get the right conjuct of h19 based on <expert-advice>.
  let h20 := h19.right
  -- False on the left can always be used.
  apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40837461323789181548976539541 : ((((p3 → ((((p3 ∨ p2) ∧ True) ∨ (((p4 ∨ (((p3 ∧ p3) → False) → p4)) ∧ (p5 ∧ (p1 ∨ True))) ∧ p4)) ∧ p5)) → False) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157902246073623223124400555083 : ((((((p1 ∧ p5) → (True ∧ p4)) ∧ (p2 ∨ p5)) → p2) → (((True ∨ p4) → (p4 → p2)) ∨ p3)) ∨ (p3 → (p3 → ((p4 → p4) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178347914200358876583447375677 : (((p2 ∧ (((p1 ∨ p5) ∨ (True ∨ (p2 ∨ p3))) ∨ p4)) ∨ (p5 ∧ True)) ∨ ((p4 ∨ ((False ∧ p1) → ((p1 → (True → True)) ∧ p4))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196876143454804931276018329082 : (((True → (((False ∨ p1) ∨ False) ∨ p4)) ∧ p5) ∨ (True → (p2 → (p4 → ((((p1 ∧ p1) → (p4 → False)) → (p4 ∧ p2)) ∧ (p4 ∨ p3)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785344685499651612842947673835 : (((p4 ∨ (((((p1 ∧ (((p5 → p5) ∨ p4) ∧ p2)) ∧ ((p3 ∧ p2) ∧ (True ∨ p3))) ∨ (False → ((p3 ∧ True) ∨ p4))) ∨ p5) ∨ False)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622531368100664454313388975902 : ((((p3 ∧ (p4 → (((p3 ∨ ((p5 ∧ (True ∧ p5)) ∧ (False ∨ True))) ∧ p2) ∧ ((p1 ∨ ((p4 → False) ∨ (p4 → p5))) ∨ True)))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64683363798001222694868030856 : ((p1 ∨ (p4 ∨ (((p3 ∨ False) ∨ (p1 ∨ ((False ∧ p1) → False))) ∧ ((((((True ∨ p5) → p3) ∧ False) → p2) ∨ p2) ∧ (p3 ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358457834868001946478099215729 : (p5 → (p1 → ((((((True ∨ (True ∧ ((p5 ∨ p1) ∨ (p4 ∧ p1)))) ∨ True) → False) ∨ ((False ∧ p3) ∨ ((p3 → p3) ∧ False))) ∧ p5) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49041867130075476530596795291 : ((((p4 ∨ (p3 ∨ ((((p3 → (p2 → (True ∨ ((p2 ∧ p3) → (p4 ∨ False))))) ∧ False) → p5) ∨ p5))) → p2) ∨ ((False → p3) ∧ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1472633580089795997913619402 : ((((p2 → (p5 ∨ p5)) ∧ (((p4 ∧ (p5 → p4)) ∧ (p4 ∨ ((p3 ∧ p1) ∧ (p3 ∨ p3)))) → (p1 ∧ p2))) ∨ False) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740618342201580849262173658048 : ((((p2 ∨ p1) ∨ (p1 ∨ ((((((p4 ∧ (p4 ∧ (True ∨ (p4 → (p3 ∧ p1))))) → p2) ∨ p3) ∧ p4) → p5) ∨ (False → (p1 → p2))))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621200368181949655354575845560 : ((((True ∧ ((((p4 ∨ True) → p4) ∧ (p2 ∨ (((p1 ∨ p2) ∧ p2) ∨ (((((False ∨ p5) ∨ True) ∨ p4) ∨ p5) → True)))) ∨ True)) ∨ p4) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65739629466738388913804627443 : ((p4 ∨ ((((p3 ∧ p5) ∧ (True → ((False → ((p3 → True) → (True → ((p5 ∨ p4) ∧ p2)))) ∧ p4))) ∨ False) ∨ ((p2 ∨ True) ∨ p3))) ∨ False) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118299048879990172917993324054 : ((p1 ∨ (p4 ∧ (((((((False ∧ (p4 → False)) ∧ p5) → p2) → p4) ∨ p3) → ((p3 ∨ p4) ∨ (p2 → (p2 ∨ False)))) ∧ False))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127965908346273276912219346220 : ((p1 → ((((True ∨ (p4 ∧ p5)) → (p5 ∨ True)) ∨ (p3 ∧ ((p3 ∧ True) ∧ (False ∧ ((True ∨ p5) → (p2 ∧ True)))))) ∧ p5)) → (p1 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114623944033351188260173384679 : ((((p1 ∧ ((((p2 → False) ∧ (p3 → (p5 → p3))) ∨ p1) ∧ (p5 ∨ p4))) ∧ p4) ∨ (p5 ∧ (p2 ∧ ((p5 ∨ True) → p2)))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355876884328877324370642600397 : (p5 → ((False ∧ ((p4 ∧ (p1 → (((p5 → True) → (((False ∨ p2) ∧ (p3 ∧ False)) → p1)) ∧ p4))) ∧ (p2 ∧ p4))) ∨ ((False → True) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111809640494404736906465086348 : (((((p5 ∨ (p1 ∧ (p5 ∨ p1))) ∧ (((((p1 ∧ (False ∧ p2)) ∨ True) ∧ p1) ∧ (False ∨ p4)) → True)) → (p4 ∨ p2)) ∨ True) ∨ (p2 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151243121570972154056059562023 : ((((p1 ∧ True) ∨ ((p2 ∨ (((p5 → (True ∧ False)) ∨ False) ∧ (True → p3))) → (p3 → (p3 → True)))) → False) → (p5 ∨ ((p5 ∧ p5) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∧ True) ∨ ((p2 ∨ (((p5 → (True ∧ False)) ∨ False) ∧ (True → p3))) → (p3 → (p3 → True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10048472576102166008369149828 : (((p5 ∧ ((p2 ∧ (((((p3 ∨ True) ∧ (p4 ∨ (p3 ∨ p5))) ∨ (p1 → p4)) ∨ (True ∨ (p4 → p5))) ∨ (p3 → p3))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116084398467160749141000163819 : ((((p4 ∧ p4) ∨ p5) ∧ (p1 ∨ ((p5 ∧ p2) → ((p4 → (p5 ∧ ((p1 ∨ ((p5 → True) ∨ p1)) ∨ p3))) ∧ (p1 ∧ p2))))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233846691795662029701093397795 : ((p4 ∨ (p2 ∧ p2)) → (((((True ∨ ((False ∨ p3) ∨ p5)) → (((True ∧ p1) ∨ False) ∧ p1)) ∨ False) → p1) → ((False ∨ (p5 ∨ p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209183486590685137281094876142 : ((p4 ∨ (((False → p4) ∨ p3) ∨ p4)) → ((p5 ∨ p3) ∨ ((p3 → p5) → (p1 ∨ (((((p1 ∨ (p2 ∨ False)) ∨ p4) → p2) ∧ False) → p1))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341071804339761433638780391156 : (p2 → ((p5 ∨ (((False → p2) ∧ (p2 → (True → p4))) → (((p1 ∨ (((True ∨ p2) ∧ p1) → p3)) ∨ False) ∨ ((p3 → True) ∧ True)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50653153855205938520518244833 : (((((p4 → p3) ∨ ((p2 ∨ p5) → (p1 → (p4 ∨ p5)))) → (((False ∨ p4) ∨ (p2 → p4)) ∨ True)) → (((False ∨ True) ∧ p4) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64519066037784588663203451128 : ((p1 ∨ (((p3 ∧ ((p3 ∨ p3) ∧ ((p3 ∧ p5) ∧ True))) ∨ p3) ∧ (((p1 → (p5 → p3)) ∨ ((p2 ∨ p2) ∨ (p1 ∧ False))) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329707580760661994355157364368 : (True → ((True → p5) → (((p5 ∧ ((((p1 ∧ True) → p5) ∧ ((False ∧ p4) ∨ p2)) → p5)) ∧ ((((p3 → p1) → p3) ∨ p1) ∨ True)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h12
    -- One of the premise coincides with the conclusion.
    exact h13
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324249391734885825533073896047 : (p5 ∨ ((((p1 ∧ ((p3 ∨ p3) ∧ p4)) ∧ p5) ∧ p1) ∨ (p2 ∨ (((p5 ∧ (p4 ∧ True)) ∧ (True ∧ p4)) → (p5 ∨ (p1 → (p4 → p4))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41748802757514429708887345002 : (((((p3 ∧ (p4 ∨ p2)) ∧ True) ∨ ((False → (((((((False → p4) → p1) ∨ p5) ∨ p1) → p5) → p1) → p4)) → (p1 → False))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320318898079188915131655980468 : (p4 ∨ ((p2 ∨ p2) ∨ (((p3 → p4) → False) → (((p1 ∨ (p1 → ((False ∧ p1) → (((p4 ∧ (p4 ∧ True)) ∨ p1) ∧ p4)))) → p1) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p1 ∨ (p1 → ((False ∧ p1) → (((p4 ∧ (p4 ∧ True)) ∨ p1) ∧ p4)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
    -- Conjunctions on the left can always be decomposed.
    let h8 := h5.left
    let h9 := h5.right
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619291631895863251600642764278 : ((((((p1 ∧ p4) ∨ p4) → (((True → ((True ∧ p1) ∨ (p1 ∨ ((p5 ∨ (((p4 ∨ p5) ∨ True) ∨ p1)) → p4)))) → p5) ∧ p1)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587584357321420933868576477806 : ((((((((p5 ∨ (False → True)) → (p1 ∧ (((p4 → p2) ∧ ((p1 ∧ False) ∨ (p4 → p3))) → (p5 → p4)))) ∧ p5) → False) ∨ True) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356247219289923804026507318813 : (p5 → ((((p4 → (False ∨ False)) → ((True → (p1 ∧ p4)) ∧ ((p1 ∨ p2) ∨ p4))) ∧ True) ∨ (((p3 → (p4 ∨ (p5 → p5))) ∨ p1) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300439759069878781009004470563 : (False ∨ (((True ∨ (((p2 ∨ True) → (p3 → (p3 → p3))) ∨ (p4 → (False → (p2 ∧ (p3 ∧ p1)))))) ∨ (False → True)) → ((p4 → False) ∨ True))) := by
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
theorem thm_5_vars_40466811055851186420498221535 : ((((((p4 → False) ∨ p5) ∨ (((True ∨ False) ∧ (p3 ∨ (p3 ∧ (False ∧ ((p2 → ((True ∧ p1) → True)) ∨ True))))) ∨ p1)) ∨ True) ∨ False) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161245897335088246167521842953 : (((p4 ∧ p4) → ((p5 → (True ∧ (p4 ∨ ((True → ((p3 ∨ (p4 → p3)) → True)) → p1)))) ∨ False)) → (((p3 → False) ∧ False) ∨ (False → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204149138048010248415899550256 : (((((p3 ∨ p2) ∧ p1) ∨ p1) ∧ p3) ∨ (((p1 ∨ (p2 → (p4 ∧ ((p3 ∨ p4) → True)))) → (True → (False ∨ (p4 ∧ False)))) → (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245666302353376253043621918235 : ((p3 ∧ p1) ∨ ((((p3 ∨ (((p2 ∨ (p2 ∧ False)) → False) → ((p1 ∨ True) ∧ p4))) ∨ True) → p1) → (p2 → (p4 ∨ (False → (True ∧ p5)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57902478653657779896215615504 : (((p4 ∨ (p1 ∧ p4)) → ((False ∨ p5) → ((False ∨ ((True ∧ (((p4 ∧ False) → (p2 ∨ p5)) → (True ∧ False))) ∨ (p5 ∨ True))) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180655692227375383133733951366 : (((False ∨ ((True ∧ p3) ∨ (p1 → True))) ∨ ((p2 ∧ (p1 ∨ p3)) ∨ p1)) → (((p2 → (p3 ∨ True)) → p2) ∨ ((False → (p1 ∧ p3)) ∨ p4))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h8
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h8
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h10
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h10
        -- False on the left can always be used.
        apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h16
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h18
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h20
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h20
      -- False on the left can always be used.
      apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204451417127951176571483828618 : ((((True ∧ (p5 → p1)) ∧ p4) ∨ p3) ∨ ((p2 ∧ (p5 ∨ ((False ∨ p3) ∧ ((p5 ∨ ((p1 ∧ p4) ∧ (p5 → True))) ∧ False)))) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46976917652761557065463399518 : ((((((p4 ∧ (p5 ∧ ((p2 ∨ (p3 ∨ p3)) ∧ p3))) → ((p3 → p2) ∨ ((p3 → p1) ∧ p3))) ∧ (p2 → p4)) → p3) ∨ (p5 → p5)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601439105441752732411458718272 : ((((p3 ∧ (((p4 → (((p4 ∧ p3) ∨ p1) ∨ (p3 ∨ (p5 → (p4 ∨ (p5 ∨ (p2 ∧ (p3 ∧ p2)))))))) ∧ (p1 → p1)) ∧ p2)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



