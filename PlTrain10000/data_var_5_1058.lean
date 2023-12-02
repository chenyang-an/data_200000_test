variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172160810821413909332054192607 : (((((True ∧ p4) ∨ ((False ∧ (True ∧ False)) ∨ False)) → False) ∨ ((False → p3) → p4)) ∨ ((p1 ∨ (False ∨ (((False ∨ False) → p2) ∨ True))) ∨ p1)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319233444899589045465824765047 : (p4 ∨ (((((p3 ∧ p1) ∧ p4) ∨ ((((p3 → p1) ∧ p3) → False) ∨ (p3 ∨ False))) ∨ True) ∧ (p4 → (((False → p1) ∧ (p4 ∨ False)) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38200977908277450056076558860 : ((((((((False ∨ p5) ∧ (p4 → (False ∧ p3))) ∧ ((p5 ∧ (p3 → p2)) ∨ p5)) → (p2 → False)) → p1) → (p2 ∨ (p5 → p4))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135506181696476893308198792953 : (((p4 ∨ ((p5 ∨ (p5 → (p1 ∧ (p1 ∧ (((True ∧ (False ∧ p5)) ∧ p1) ∨ p5))))) ∧ p1)) → (p1 ∧ (p5 ∨ p3))) ∨ (p2 → (p2 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670279768717645212392403005421 : (((((p4 ∨ ((False → p5) ∧ p3)) → ((True ∨ p5) ∧ (((p3 → (p3 ∧ p1)) → p4) ∨ ((p4 ∨ p2) ∧ p1)))) ∨ ((p1 ∧ p1) → True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_49375929649832621703762370938 : (((p5 → ((p5 ∧ ((True ∧ False) → (p1 → p2))) → (p1 → ((((p2 ∧ (p1 → False)) ∧ p3) → p5) → p2)))) ∨ (p5 ∨ (True ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731557797765443435305849877722 : ((((False → (False → False)) → (((True ∧ p5) ∨ ((p5 ∧ ((True → p2) ∧ ((True → p3) ∨ p2))) ∧ p2)) ∨ (p1 → (p3 ∧ (p2 ∧ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64510734555588887652147111085 : ((p1 ∨ ((((False ∨ (False ∨ (p1 → p3))) ∧ p4) ∧ ((p3 ∧ p3) ∨ p1)) ∧ (((((p4 ∧ p2) ∨ False) ∧ False) → p2) ∨ (True ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655391774173242433739310033856 : ((((((((((p1 ∧ (p2 ∨ p3)) ∨ (True ∧ p5)) → p3) ∧ False) ∨ (p4 ∧ p5)) ∧ (p3 ∧ (p4 → p4))) ∨ (p2 → False)) ∨ (p5 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708899938195155963615883925506 : ((((((p5 ∨ (p5 → p1)) ∨ True) ∨ (p1 → False)) → ((p2 ∨ (p2 ∨ ((True ∧ p3) ∧ (((p3 ∧ True) ∨ (p2 ∧ p3)) ∨ p2)))) ∨ True)) ∨ p4) ∧ True) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148492283866530191630843272763 : ((((True → ((p3 ∨ (p4 → p3)) ∨ False)) ∨ ((False ∨ False) ∨ False)) ∨ ((((p4 ∧ p3) ∨ p5) ∨ p3) ∨ p5)) ∨ ((True ∧ p2) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179426127858762548103289855016 : ((p4 ∨ (((p4 → p4) → p2) → (((p5 ∨ p4) ∧ p5) ∧ (p3 ∧ p2)))) ∨ (False → (False ∧ (((p1 ∧ True) ∨ p5) ∨ ((p5 ∧ False) ∨ p5))))) := by
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
theorem thm_5_vars_592794983387726996020878359598 : ((((((p3 → (((p2 → (False ∨ ((False ∨ p4) → p5))) ∧ (p4 ∨ p1)) ∧ (p2 ∧ p5))) ∨ (p4 ∨ False)) ∧ ((p2 → p3) ∧ p3)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110778180840855742278821961204 : ((((((p5 → p1) → ((((p4 ∧ ((p2 → p3) ∨ p1)) → True) → (p4 → p2)) ∨ (False → (p2 → p4)))) ∧ False) ∨ p3) ∧ p3) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117677002446499533133554305937 : ((p3 ∧ ((p3 → ((False → False) ∨ (p2 ∧ (p5 ∧ p5)))) ∧ ((((p3 ∧ p4) → (((p1 ∧ p5) ∨ True) ∧ True)) → p1) → False))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721741893723049264782930389295 : ((((p1 ∨ ((p4 → True) → p1)) → (((p3 → (p2 ∧ p2)) → (p3 ∨ ((p5 → p5) ∨ False))) ∧ (True ∧ (((p5 → False) ∧ p2) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115034367753317896917221525729 : ((((((True → (((p2 ∨ p2) ∧ p2) → False)) → p5) ∨ True) ∧ p3) ∨ ((p4 → p1) → ((p2 ∧ ((p2 ∨ p3) ∧ False)) ∨ p1))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266025453999173006568731645773 : (True ∧ (p1 → ((p4 ∧ (True ∨ ((True ∧ p3) → True))) → (((((p1 ∨ (False → p3)) ∧ p2) ∧ (((False → p3) ∨ p4) → p2)) → p3) ∨ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352651907877120322384186658367 : (p4 → ((p4 ∧ p2) ∨ ((((True → (p3 ∨ ((p3 ∧ p3) ∧ (((False ∨ p2) ∧ (p3 ∨ p5)) ∨ p4)))) → p3) → p2) ∨ (p1 → (p2 → p2))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_557584392355803833284826962 : (((p5 ∧ (((p4 ∨ False) ∧ (((p1 ∧ ((p3 ∧ (True → p3)) → p5)) → p3) ∨ (p5 ∨ (False ∧ (p5 ∧ p1))))) ∨ p2)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113270693277616856479955504563 : ((((((p2 ∨ (p5 ∧ (p3 ∨ p5))) ∨ (p1 → ((p3 ∧ p4) ∧ p2))) ∧ p3) ∧ ((True → p3) ∨ (True ∧ p2))) ∧ (False ∨ True)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_15670631823268429791264527648 : (((((p5 ∨ ((p5 ∧ (p5 ∨ p4)) → (p5 → False))) → p4) ∧ (((((p1 → p2) ∨ p4) → p4) ∧ p2) → (p1 → True))) → (p2 ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759785164120668385398785272417 : (((p2 ∧ (((((p4 → p1) → ((p4 → p3) → p3)) ∧ False) → p3) → ((p5 → (((p1 → p4) ∧ ((False ∧ p4) ∧ True)) ∨ True)) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137309976023262425757532728504 : ((p2 ∧ (((p4 ∨ ((p4 ∨ p5) → ((p1 ∧ p5) ∨ (False → True)))) ∧ p1) → (p1 → (p1 → (False ∧ (True ∨ False)))))) ∨ ((p3 ∧ True) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192437114591651020500183932780 : ((((((True ∨ True) ∧ p3) → (p3 ∨ p1)) → False) ∨ p2) → ((p5 ∨ (True ∧ (((p5 ∧ p3) ∨ ((False → True) ∨ (p5 ∧ False))) → p5))) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192279875739139950521723544678 : ((((p2 → p2) ∧ (p4 ∧ (p1 ∨ (p5 → True)))) ∧ p1) → ((p5 ∨ ((p4 ∨ p5) → ((((p1 → p2) → True) → p2) → (True → p2)))) ∨ p5)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h12 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h13 : ((p1 → p2) → True) := by
        -- Implications on the right can always be decomposed.
        intro h14
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h15 := h10 h13
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h17 : ((p1 → p2) → True) := by
        -- Implications on the right can always be decomposed.
        intro h18
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h19 := h10 h17
      -- One of the premise coincides with the conclusion.
      exact h19
  case inr h20 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h21
    -- Implications on the right can always be decomposed.
    intro h22
    -- Implications on the right can always be decomposed.
    intro h23
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h24 =>
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h25 : ((p1 → p2) → True) := by
        -- Implications on the right can always be decomposed.
        intro h26
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h27 := h22 h25
      -- One of the premise coincides with the conclusion.
      exact h27
    case inr h28 =>
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h29 : ((p1 → p2) → True) := by
        -- Implications on the right can always be decomposed.
        intro h30
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h31 := h22 h29
      -- One of the premise coincides with the conclusion.
      exact h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111101687240377827015682331884 : (((((False ∨ (((p5 ∨ p5) ∨ p3) ∨ p2)) ∧ (True ∧ p3)) ∧ (((True ∧ p2) → ((p2 ∧ False) → p2)) → (False → p5))) ∧ p5) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262469205335594236764391759612 : (True ∧ ((p3 ∨ ((False → (p5 ∧ p3)) → (p5 ∨ (p3 ∨ ((p2 → (True ∧ (((p2 ∧ p2) → (p4 ∨ p5)) → p4))) ∨ (False → p3)))))) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246254604131774991607682275810 : ((p4 ∧ p4) ∨ (((p1 ∨ (((((p1 ∨ True) → p4) ∧ (p2 → p5)) ∨ p1) ∧ p1)) ∨ (((((p4 ∨ p4) ∨ p2) ∧ False) ∨ p4) → p4)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h4
      case inr h7 =>
        -- False on the left can always be used.
        apply False.elim h4
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4572236631912335315744020986 : (p4 → (((p1 ∧ (p4 ∨ p3)) ∨ (((((p5 ∧ True) ∨ (p2 ∧ p2)) → ((p4 ∧ (False ∧ p1)) ∧ False)) ∧ (False ∨ p3)) ∨ p4)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356036489825727406476496995714 : (p5 → (((p4 ∧ (True → p5)) → ((p3 ∨ (p3 ∧ p3)) ∧ (((p2 → p1) ∨ (p3 ∧ p1)) → (p2 ∧ False)))) ∨ ((p3 → p3) ∨ (p4 → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645713963481768273778178215163 : ((((p5 ∨ (((p4 ∨ True) → (p2 → (p3 → (p1 ∧ p4)))) ∧ (False → ((((True ∨ False) → p3) ∨ (p1 → p4)) ∧ (p3 ∧ p1))))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178230389380157962428314687527 : (((p3 → ((((p2 ∨ p3) ∨ p1) ∨ (p5 → (p2 ∧ p4))) ∨ p3)) → p4) ∨ ((((True ∨ (True → False)) ∧ (False ∧ False)) ∨ p1) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229943406001930393887951425126 : (((True ∧ p1) ∧ p1) → ((((p4 ∨ (((p3 → p5) → p2) → p3)) ∧ False) ∧ ((p3 ∨ p5) ∨ ((p2 ∨ p3) ∧ p5))) ∨ (True ∨ (p2 ∨ p5)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325149903432409236300495212079 : (p5 ∨ (True ∧ (((((p1 ∨ p2) ∧ p3) → (p5 ∧ p1)) ∧ (p2 ∧ p5)) ∨ ((((False ∨ (True ∨ (p4 ∨ p4))) ∨ p2) ∨ (p2 ∨ p1)) ∨ p4)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622672868040680927418804632322 : ((((p4 ∧ (((p3 ∨ p4) ∨ ((False → (False → (p1 ∨ p1))) → p5)) ∧ (((p4 → p4) ∨ ((p3 ∨ (p1 → p3)) ∨ False)) ∨ False))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347472879390687797606376881651 : (p3 → ((((True ∧ False) ∧ (False ∨ p1)) ∨ p4) ∨ ((((True ∧ ((True → (False ∨ False)) ∨ p3)) ∨ p5) ∨ p3) ∧ (p4 → ((True ∨ p5) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135711319186966693288879698654 : (((p2 ∧ (p5 ∨ (((p1 ∧ p4) → (p5 ∨ p3)) ∨ ((False ∧ False) ∨ p4)))) ∧ ((p3 ∨ (p5 → (p3 ∧ p4))) ∨ False)) ∨ ((p2 ∨ False) → p2)) := by
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
theorem thm_5_vars_53762050403691639392655145009 : ((((p1 ∨ (p1 ∧ (((p4 ∨ False) ∨ p3) ∨ p3))) ∧ p1) ∨ ((p3 ∨ ((p2 ∧ p5) → False)) → ((p2 ∧ p5) → ((False → p1) ∧ p3)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (p2 ∧ p5) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h4
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57947535008557171523015360891 : (((p1 → (p3 ∧ p3)) → ((p5 ∨ p3) ∧ (True → ((((((False ∨ ((False → False) ∨ p2)) ∨ p4) → (p3 ∨ False)) → p2) ∨ p2) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111666505380280731323200499171 : ((((p3 ∨ ((((False ∧ ((p3 ∧ False) ∨ True)) → ((p1 ∨ p4) ∧ True)) → (p5 → ((p2 → False) ∧ False))) ∨ True)) ∨ False) ∨ p1) ∨ (p4 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_135091553987385561425635898867 : (((((((True ∨ p5) → ((True ∨ p2) ∧ p3)) ∧ p2) ∧ p1) → ((True ∧ (p5 ∧ (p4 → p1))) ∧ p2)) ∨ (p1 ∧ True)) ∨ (p1 → (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320291957887969776506051853844 : (p4 ∨ ((p4 ∧ p4) ∨ ((((p4 ∧ ((p3 → ((p1 ∨ ((p3 ∧ True) → (p5 ∧ (p5 → p2)))) ∧ p1)) ∨ False)) ∨ (p3 ∧ True)) ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324730138024149452651900179579 : (p5 ∨ (((p3 → True) → p5) → ((p4 → (((p1 → (p2 ∨ ((((False ∧ p2) ∧ (True ∨ (p1 ∧ p3))) ∧ False) ∨ p5))) ∧ True) ∨ True)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206033838342893769589251526036 : ((p2 ∧ ((True ∨ p4) → (False ∨ p1))) ∨ ((p2 ∨ (p5 ∧ (p1 ∧ ((False → (p1 ∨ (((p1 ∧ p1) → p3) ∧ p5))) ∧ p2)))) → (p3 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765551612901736293908329546324 : (((p4 ∧ (((False ∨ p3) ∨ (((False → ((True → p3) ∧ ((p5 → False) ∨ p3))) ∧ p4) ∧ p2)) → ((p3 ∨ ((True ∨ p2) ∨ False)) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64197348799192810901839115550 : ((False ∨ (False ∧ ((True → False) ∨ ((((False ∧ p5) ∨ ((((False ∧ True) → p4) → False) ∨ (p5 → p4))) ∨ p2) ∧ (p5 ∧ (p4 ∨ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76584377720913269573474253282 : (((((p3 ∨ ((False ∧ (True → (p4 → (p2 ∨ ((True ∧ p5) ∧ True))))) ∨ (p1 ∨ True))) ∨ p2) ∨ (False ∧ (False ∧ (p5 → False)))) → False) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 ∨ ((False ∧ (True → (p4 → (p2 ∨ ((True ∧ p5) ∧ True))))) ∨ (p1 ∨ True))) ∨ p2) ∨ (False ∧ (False ∧ (p5 → False)))) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172818253402125979361631050553 : ((True ∧ (((False → (p1 ∨ p3)) → (p4 ∧ p1)) ∧ ((p1 → (p3 ∧ p1)) → True))) ∨ (False ∨ (((((p5 ∧ False) ∧ p3) → p3) ∨ p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65095053193489029593617199808 : ((p2 ∨ (p2 ∨ (((((p3 → (((False ∧ (False ∧ p3)) ∧ True) → p3)) ∧ (p1 ∨ (p3 ∧ False))) ∨ p3) → (p1 ∧ (p1 ∧ p1))) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736671267398897035696873298616 : ((((p2 → True) ∧ (((p2 ∨ p3) ∨ (p5 → p5)) ∧ (p5 → ((p2 ∧ False) ∧ (p3 ∧ (True → (((p1 ∨ p5) → False) ∧ (p3 ∨ True)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110122477167171494367557481346 : ((p1 → (((((p3 → True) → (False ∧ p4)) ∨ True) → (((((p2 ∧ p4) ∧ p2) ∨ (p3 → p4)) ∧ p5) → (p3 ∨ p2))) ∨ True)) ∧ (False → p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_884959387922636709629768906 : ((p1 → (((p4 ∧ ((p4 ∧ ((p4 ∨ p5) → p4)) ∨ False)) ∧ (False → (p1 ∧ (((p4 → p1) → p2) → (False → p5))))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625149549018724334894731177561 : ((((True → (((((True ∧ p1) → (p3 ∨ ((False ∨ p3) → p1))) ∧ p1) → True) → (False ∧ ((p1 → (p2 → (False ∨ p1))) ∧ p1)))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41839629014564954199510773697 : ((((False ∨ (p4 → False)) ∧ (p5 → (p5 → (((p1 ∧ (False → p4)) → ((p3 → (True ∨ p3)) ∧ p4)) ∨ (True ∧ (p5 ∧ p1)))))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18940108442795187464890531983 : (((False ∨ ((p3 ∧ True) ∧ (p2 ∧ ((False → False) ∧ (p3 ∨ (True ∧ (p2 ∨ (p4 ∧ p4)))))))) ∨ ((False ∨ False) ∨ (p1 ∨ (False → p1)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147815816914115576787189684794 : (((p5 ∧ ((((True ∨ p1) → (p1 ∧ (p3 ∨ (((p4 → p2) → False) ∧ p2)))) ∧ (p2 → p5)) ∨ False)) → p4) ∨ (((p2 ∧ False) → p1) ∨ p3)) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66479063287178117006778062471 : ((True → (((((True → (p4 ∨ (((True ∧ p1) ∨ False) ∧ (False → False)))) ∨ ((p4 → p3) ∨ (p2 ∨ (p3 ∧ p1)))) → p4) → p5) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637277176424018712425849767531 : (((((((p1 → ((p1 ∧ p4) ∨ p5)) ∨ False) ∨ ((True ∧ p3) ∨ True)) → (((p2 ∧ True) → ((p2 ∧ (p2 → p3)) ∨ p2)) ∨ p5)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49793776036113418283419455143 : (((p5 ∨ ((p3 → ((((p2 → p3) ∨ (((True → p2) ∧ p4) ∨ p3)) → p5) → (p4 ∧ p3))) ∧ (p5 ∧ p1))) → (False ∧ (p2 ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717123481577204696539133296666 : ((((False ∨ (p2 ∧ (True ∧ p4))) ∧ (p1 ∨ ((((p2 → ((((p1 ∧ (True ∨ False)) ∨ False) ∧ p4) ∧ False)) ∨ (False ∧ p1)) ∨ p4) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52363095754881073058232531391 : (((((p1 ∨ p3) → ((((False ∨ p1) ∧ True) → p3) ∧ p1)) ∨ (p3 ∧ p5)) ∧ (((p1 → (False ∨ False)) → (False ∨ p5)) ∨ (p4 ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45424025409013839197536314416 : (((True ∨ ((((p4 → ((p1 ∧ (p4 ∨ p5)) → False)) ∧ True) → (p4 ∧ ((p5 ∧ p2) ∨ ((p2 ∨ p3) ∨ (p4 ∨ False))))) ∧ True)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55872194886444437479256798366 : (((True ∨ ((p4 → False) ∨ p4)) ∧ ((((p3 ∨ (False → ((p1 ∨ p2) ∨ p4))) → (True ∧ p5)) ∨ (p1 ∨ True)) → (p4 ∨ (p3 ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323663223329495183768478307453 : (p5 ∨ (((((p4 → ((((p1 ∨ p2) → p1) ∧ (p3 ∨ p2)) ∧ p2)) ∧ p3) ∨ False) ∧ ((p2 ∨ p2) ∧ p5)) ∨ (p4 → (p3 → (p3 ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198007862316620237416595309067 : (((p1 → p2) ∧ ((p2 ∧ True) → (p3 ∨ p4))) ∨ (((p1 ∨ p2) ∨ (((p1 ∨ p1) ∨ (p4 ∨ ((True ∨ False) ∧ p1))) ∧ False)) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350994047221786570452851235808 : (p4 → ((p2 ∧ (p3 ∨ (((((False → False) ∧ True) → (p5 ∨ (((True ∧ p3) ∨ (p4 ∨ p5)) ∧ (p1 ∧ p3)))) → p3) → p1))) ∨ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37445153095923283781433467832 : ((((((False ∧ ((False → (p5 → (True → p4))) ∨ (p2 ∧ True))) ∧ (False → p1)) ∨ (((p1 ∧ p4) → p2) ∧ (p2 → True))) ∨ True) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115109324970255559934053860084 : ((((p5 → (((p1 → p5) ∧ ((p3 → p1) ∧ p3)) → True)) ∨ p5) → ((p5 → (False → (p4 → p4))) → ((p3 → p1) → p3))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612115834854842749639283773754 : ((((((((False → p2) ∨ (p3 → ((p2 ∧ (True → (True ∧ (p3 ∧ p4)))) ∨ False))) ∨ p2) → ((p4 ∧ p3) ∨ p3)) ∧ (True → p4)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_809296324389494738808871193306 : (((p5 → (((p1 → p2) ∧ (((p3 → p1) ∨ p3) ∨ ((p3 ∧ (p2 ∨ p2)) → (p1 → (((p5 ∨ p5) ∧ p5) ∧ (False ∧ p3)))))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233522310445379695035030362838 : ((p1 ∨ (False ∨ p4)) → ((False ∧ (p5 ∨ p5)) ∨ (((((((True ∧ False) ∧ p4) ∨ p4) ∨ p4) ∧ False) → False) ∨ ((p5 ∨ True) ∨ (p2 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
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
theorem thm_5_vars_4232231999980093347683193006 : (p5 ∨ ((False → (((p4 ∧ p5) ∧ p1) ∨ True)) ∧ ((p1 ∨ (p3 ∨ p4)) ∨ (p2 ∨ ((((p5 → True) → (p5 → p4)) ∧ False) → p5))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704318278827879156771388946825 : ((((((True ∧ True) ∨ (False ∧ True)) ∨ (False ∧ (p2 → p3))) → ((p1 ∧ p2) ∨ (((p5 ∧ ((p2 ∧ p4) → True)) ∨ p1) ∨ (p5 → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256371246293722955260903376870 : ((False ∨ p2) → ((p5 → p3) → ((((p1 → p4) → p1) ∨ (True ∨ (p2 → (((p4 ∨ ((p3 ∨ True) ∧ p2)) ∧ p4) ∧ (p1 → p2))))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184125264350323280391053317614 : (((False ∧ ((p1 ∨ ((p3 ∨ (p4 ∨ p3)) → p2)) → p4)) ∨ p1) ∨ ((((p4 → False) ∨ ((p2 ∨ p3) → p2)) ∨ (p3 ∨ (p3 ∨ True))) ∨ p5)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119134415843492154122689737177 : ((p1 → (p2 ∨ ((False ∧ (p4 → False)) ∨ (((p2 ∧ p5) ∨ ((True ∨ ((True → p5) → True)) ∧ (p5 ∧ p2))) → (p3 ∨ p3))))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48955693162789322340577199736 : ((((True → (((p3 → False) ∨ p3) → ((p1 ∧ (False → ((p5 → (p4 ∧ (True → p5))) ∨ True))) → p3))) ∧ False) ∨ ((False ∧ p4) → p3)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_115908273517139068988784591758 : ((((p3 ∧ False) ∧ (p1 → p3)) ∨ ((((True ∨ True) → False) ∧ ((((p3 ∨ (p3 → True)) ∨ (True ∧ p4)) ∨ p3) ∨ p1)) → False)) ∨ (p3 ∨ p4)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h8 : (True ∨ True) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h9 := h2 h8
          -- False on the left can always be used.
          apply False.elim h9
        case inr h10 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h11 : (True ∨ True) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h12 := h2 h11
          -- False on the left can always be used.
          apply False.elim h12
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h16 : (True ∨ True) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h17 := h2 h16
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h19 : (True ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h20 := h2 h19
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h22 : (True ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h23 := h2 h22
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226013607885971347497874048978 : (((p4 ∧ p2) ∨ p2) ∨ ((p4 ∨ (p4 ∨ (False ∨ ((True ∨ p5) ∨ ((True ∧ ((p4 ∧ p2) ∧ p3)) ∨ ((True ∨ True) ∨ p4)))))) ∨ (p4 ∨ p5))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245362058666478953731217815871 : ((p2 ∧ p3) ∨ ((((True ∨ (p5 ∧ p5)) → (((True ∧ p1) ∨ p2) → ((p3 → False) ∨ p2))) ∧ False) ∨ (((False → p4) → (p5 ∨ True)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149978031338933847617178469590 : ((p4 ∨ ((p5 ∧ (p3 ∨ (p1 → p1))) ∧ (False ∨ ((p4 → (p4 → p4)) ∧ ((p4 ∨ p1) ∧ (p1 ∨ True)))))) ∨ (True ∨ ((p2 ∧ False) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50028949273415173407013343221 : ((((((p5 → p2) ∧ p4) ∨ p1) → (((p5 → True) ∨ p5) → ((((p2 ∧ p1) → p4) → p4) ∧ p1))) ∧ (False → (p2 → (False → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657309433210533275663775230905 : (((((p4 ∧ p1) ∧ (False ∨ (((False → p4) ∧ ((p3 → ((p3 ∨ ((p5 → False) ∧ (True → p2))) ∧ p1)) ∨ p2)) ∧ p4))) ∨ (True ∨ p3)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_138798126828041488517336591303 : ((((False → True) → ((p5 ∧ p3) ∧ ((True ∧ (((False ∧ (p4 ∨ p4)) → p3) → p1)) ∧ ((True ∧ False) ∧ True)))) ∧ p4) → ((p4 ∨ p3) ∧ p2)) := by
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
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (False → True) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339006765164495113566614276554 : (p1 → (True ∧ ((((((p3 ∧ p4) ∨ p2) ∧ (True ∧ ((False ∧ p1) ∧ (p2 ∧ p3)))) ∨ (False → (p5 → (True → True)))) ∨ p4) ∨ (p3 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52812499418539415133580956315 : (((((p4 ∨ (p5 ∧ True)) ∨ (p1 ∨ p2)) → (((p3 ∧ True) → p5) → p2)) → ((p5 → ((p1 ∨ p5) ∧ ((p4 → p4) → p3))) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197121034424125398726779751214 : (((p2 ∨ ((True ∧ p1) ∧ (p3 ∧ p3))) ∨ p4) ∨ (((p1 ∧ ((p5 → p4) ∨ (p4 → (p5 ∨ p4)))) ∧ p1) ∨ (p4 → ((p3 ∨ p4) ∨ p4)))) := by
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
theorem thm_5_vars_147486914677443062894957779112 : (((p4 ∧ ((p5 → False) → ((p5 → p1) ∧ ((((p1 ∨ (p3 ∧ p1)) ∨ (True ∨ True)) ∧ p3) ∨ p3)))) ∨ True) ∨ ((p4 → p1) ∧ (p3 ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139450769398943185616740554834 : (((((p1 ∨ (p5 ∧ (((p3 → ((p3 ∧ p3) → (p4 ∧ (p3 ∨ (p5 → p4))))) → p4) ∨ p1))) → p1) ∨ True) → p2) → ((True → p5) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786927502330913159666649955735 : (((p4 ∨ (((p3 → p2) → p2) → (True → (p4 ∨ ((False ∧ (p5 ∧ (False ∧ (True → (p3 ∧ p2))))) ∨ (False ∧ (False → (p5 ∨ p4)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133527019249640099201349857136 : (((((((p4 ∨ ((p1 ∧ p2) ∨ (p3 → p3))) → p2) ∧ ((p5 → p2) ∧ p5)) ∨ ((p1 ∧ True) ∨ p2)) ∧ False) ∧ p3) ∨ ((p1 ∧ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42157070302054233197510117825 : ((((p2 → False) → (p3 ∧ ((((p5 → (p4 ∧ p2)) ∧ True) → (False → p5)) ∧ (((False → False) → (p3 ∧ (True ∧ True))) ∧ p2)))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166503547386387268229635494870 : ((p4 ∨ (((((p1 ∨ (p3 ∧ ((False ∨ True) ∧ (p2 ∧ p3)))) ∧ p1) → p2) ∨ False) ∧ p5)) ∨ (p1 ∨ (p5 → ((False ∧ False) → (p4 ∧ p5))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174235782532087382458963603454 : (((False ∧ ((p5 ∨ False) ∨ (((p4 → p3) → (p4 ∨ False)) ∨ False))) → (p5 → p1)) → ((((p3 ∨ p1) ∧ p3) → (p1 ∧ (p2 ∧ False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22530186542014819813593947184 : (((((p2 ∧ p4) ∨ (True ∨ p3)) ∨ p3) ∧ (((p3 ∨ (((p4 → p2) ∨ p1) ∧ ((p1 → p1) ∨ p2))) ∨ (True ∨ p1)) ∨ (p5 ∧ p4))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_351407404955264133313524710658 : (p4 → ((((((p4 ∧ p3) → (p2 ∧ p1)) → p1) ∨ p5) ∨ ((((p3 ∨ True) ∨ p4) ∧ (p5 ∨ False)) ∧ p5)) ∨ (p4 → ((p2 ∨ p4) ∨ p4)))) := by
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
theorem thm_5_vars_41207199896717676523344462049 : ((((False → ((True ∨ ((False ∨ p3) ∧ (False ∧ (((p3 ∧ (False → p1)) → p2) ∨ p5)))) → (True ∨ False))) → ((p2 → p3) ∨ p2)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_988469108664939808133951259669 : (((p3 ∧ ((((p4 → (p5 ∨ p3)) → False) → ((((p3 → (((p4 ∨ True) → True) → p1)) ∨ p1) → p4) ∨ ((True ∧ False) → p2))) → p1)) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p4 → (p5 ∨ p3)) → False) → ((((p3 → (((p4 ∨ True) → True) → p1)) ∨ p1) → p4) ∨ ((True ∧ False) → p2))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146985668170662587830109622638 : ((((True ∧ (p5 ∨ (((p5 → ((((p3 → p4) ∧ (True → p4)) ∧ p5) → False)) ∨ p5) → p1))) → p5) ∧ p5) ∨ (p2 ∨ (False → (p1 ∧ p1)))) := by
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



