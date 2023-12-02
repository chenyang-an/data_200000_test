variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775619404521826166439426143946 : (((False ∨ (False ∨ ((p5 ∨ p5) ∧ ((p5 ∨ ((((p4 → p4) ∨ (p4 → p1)) ∧ ((p1 → p4) ∨ (p4 ∧ (False ∧ p5)))) ∧ p3)) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313736031620071139913461136399 : (p3 ∨ ((p1 ∨ ((((p2 ∨ p2) ∨ p4) → (p4 ∧ False)) ∧ ((p5 ∧ ((p3 ∧ p5) ∨ (((True ∧ p4) ∧ True) ∧ (True ∧ True)))) ∧ p2))) → p1)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h13 : ((p2 ∨ p2) ∨ p4) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h14 := h4 h13
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h17.left
      let h20 := h17.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h18.left
      let h24 := h18.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h25 : ((p2 ∨ p2) ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h22
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h26 := h4 h25
      -- We need to get the right conjuct of h26 based on <expert-advice>.
      let h27 := h26.right
      -- False on the left can always be used.
      apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590311897746834782610959527429 : ((((((False ∨ (p2 → p2)) ∧ (p2 ∧ (p5 → ((((p2 ∨ p4) → (((p4 ∧ p3) ∧ True) → (p4 ∨ p4))) ∨ p1) → p1)))) → p5) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213107793440414642025559871079 : ((((p2 ∨ p5) ∧ p2) ∧ p3) ∨ (((p4 ∧ (p4 ∨ (((False → p3) ∧ ((True ∨ (True ∨ ((p3 → p2) ∧ True))) ∨ p3)) → p2))) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168656199637344161694718216048 : ((p4 ∧ (p4 ∧ (p1 ∧ (p1 ∨ (True ∧ ((((p4 → p3) ∨ False) → p1) ∨ (p4 → False))))))) → ((p5 → (False ∧ False)) ∨ (False → (p2 → p3)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h9
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Implications on the right can always be decomposed.
      intro h16
      -- False on the left can always be used.
      apply False.elim h15
    case inr h17 =>
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h18 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h19 := h17 h18
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148585175106522359826313424276 : ((((((p2 ∧ p3) → (p4 → p5)) → p2) ∧ (p2 ∧ False)) ∨ ((p5 → ((p5 ∧ False) ∧ (p3 ∨ p3))) ∧ p1)) ∨ (p2 → ((False → p3) ∨ p5))) := by
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
theorem thm_5_vars_725147059120788590832302829016 : ((((p1 → (p5 ∨ False)) ∧ (((True ∨ ((True ∧ ((p5 → (p4 ∨ p2)) → p4)) ∧ (False → p4))) → p2) ∧ ((False → p5) ∨ (p1 ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112193687301111095433427638265 : (((p5 ∧ (p5 ∨ (p3 ∨ (((p3 ∨ (False → ((p1 → (True ∨ True)) ∧ (p4 ∨ ((p3 ∧ True) ∧ p1))))) ∨ p3) → p2)))) ∨ True) ∨ (True ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165326629680195001651360106089 : ((((p3 → ((p1 ∧ (p1 ∨ p1)) ∨ (True ∧ (True ∧ p4)))) ∧ p4) ∧ (True ∧ (p3 ∨ p4))) ∨ ((((True ∨ (p2 ∨ False)) ∨ True) ∧ True) ∨ p3)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135450673045134715094918596001 : (((((True ∧ (p2 ∨ ((False → (False ∨ p5)) ∨ (p2 ∨ p1)))) ∧ ((p4 → False) ∨ p4)) ∨ False) → ((p1 → p4) → p5)) ∨ ((True ∨ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1951298100654452013964609454 : (((((((p1 → (p1 → p3)) ∨ False) → p3) ∨ ((p3 ∨ p2) ∨ p4)) ∨ (p3 ∧ p4)) ∨ (p1 → True)) ∨ (((p3 ∨ p2) ∨ p2) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733940278154062892272771238254 : ((((True ∨ False) ∧ (((((p5 ∧ (p4 ∧ (False ∨ (((p3 ∧ True) ∨ (p4 ∨ (p5 → p3))) ∧ (False → p5))))) ∧ True) ∧ p1) ∧ True) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118914359376078990518391515830 : ((True → (p5 → (p1 ∨ (p2 ∧ (p4 → (p1 → (((p3 ∨ (((p5 ∧ True) ∧ False) ∨ p4)) ∨ (p4 → (p3 ∧ p3))) ∧ p2))))))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64327227019078897489812980203 : ((p1 ∨ ((((p5 ∧ (False ∨ True)) → (p2 ∨ p1)) ∧ (p1 ∨ (((p3 → (p1 ∨ False)) ∨ ((True ∨ (p3 → p1)) ∨ True)) ∨ p3))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249654888717201328408995916527 : ((p5 ∨ p4) ∨ ((((((p3 → (p4 → p3)) ∧ ((False ∧ False) ∨ ((p1 → True) ∧ (p5 ∧ p2)))) → False) ∨ p1) ∨ ((p1 ∧ False) → p1)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40751391519824961290424601800 : (((((p4 ∧ p5) ∧ (p1 ∨ (False ∨ (p2 → (((p1 ∨ (p5 ∨ (True ∨ p3))) ∧ p4) ∨ ((p3 → (p3 → p4)) ∧ p4)))))) → p1) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174521865967111646684328627797 : (((((p1 → p2) ∨ (p4 ∨ False)) ∧ p2) → (((False ∧ p1) → p4) ∨ (p3 ∨ p2))) → ((p2 ∧ True) ∨ (True → (p3 ∨ (p4 → (p5 ∨ True)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251610386295974135992645649714 : ((p3 → p1) ∨ ((True → (True ∧ (((p4 → p1) → ((True → ((p5 → True) ∨ p1)) → (p2 → (p2 → p4)))) ∨ (True → True)))) ∨ (True ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674345037769718176925940040122 : ((((p1 ∨ ((((p3 ∨ True) ∨ True) ∨ ((p4 ∧ (p5 ∧ (((False ∨ p3) ∨ p1) ∧ p2))) → p2)) ∧ (p5 ∨ p1))) → ((p3 ∨ False) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703260582769767644273403673376 : ((((p2 ∧ (p3 → ((True ∨ p1) → ((True → p3) → False)))) ∨ (((p5 → p3) → p4) → ((((p3 ∧ p4) → p4) ∨ False) ∨ (p1 ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793574948914431967677582435240 : (((True → (p3 ∨ (((False ∨ (False → ((p2 → ((p1 → ((p3 ∧ True) ∧ (p2 → p1))) ∧ p4)) ∨ p3))) → ((p1 ∧ p5) → p1)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219567965874821094765190445270 : ((True → ((p1 → p4) ∨ True)) → ((((p5 ∧ p3) ∨ ((p4 → p1) ∧ p5)) ∧ ((p3 ∨ (((p2 ∨ p5) ∨ True) ∧ True)) → (True ∧ p4))) → p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h8 : (p3 ∨ (((p2 ∨ p5) ∨ True) ∧ True)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h14 : (p3 ∨ (((p2 ∨ p5) ∨ True) ∧ True)) := by
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
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h15 := h4 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51403200165498900901616225043 : ((((((True ∨ p1) → (False → ((p3 ∨ True) ∧ ((False → (p1 ∨ True)) ∧ p3)))) → p2) → False) → (((p2 ∧ p5) ∨ p5) ∨ (p5 → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325975896990260926897686796759 : (p5 ∨ (True → ((((p1 ∨ (p4 ∨ (p3 ∧ ((p1 ∧ ((p5 ∨ (False ∨ (False → True))) → p2)) → ((p5 → p4) ∧ p5))))) ∧ True) → p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315854776557139684128719851208 : (p3 ∨ ((p2 → p4) → ((((p4 ∧ True) ∨ (p5 ∧ (False ∧ ((True → p1) ∧ True)))) ∨ True) ∨ ((((p1 ∧ p5) → (p1 ∨ True)) ∨ p2) ∧ False)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40250943284148699841412758817 : ((((False ∨ ((p3 ∧ ((((False ∨ (p4 ∧ p2)) ∧ False) ∨ (((p3 → True) → p4) ∧ True)) → p3)) → ((p5 ∨ False) → p4))) ∧ False) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205645201178168018907525880239 : (((p5 ∧ p1) ∨ ((p2 ∨ p3) ∧ p4)) ∨ ((((((p5 ∨ p2) ∧ p4) ∨ p4) ∨ p5) → True) ∨ (((((p3 ∧ False) ∧ p5) ∨ True) ∧ p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610303548754123783336349190178 : ((((((False ∨ (p3 → (((p4 → p2) ∧ (p4 ∧ (True → ((p1 → (p4 ∨ (False ∧ p2))) ∨ p4)))) → (p3 → p2)))) ∨ False) → p1) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41084132968433410949755889385 : (((((((p3 → True) ∧ ((p4 → p1) ∧ (p4 → (((p3 ∨ p2) ∧ p3) ∨ (p3 ∧ p1))))) ∧ True) ∨ p3) ∧ (True ∨ (True → p4))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_397518374038043430634322064253 : ((((p2 ∨ (((False ∨ ((((p1 ∧ p3) ∨ p1) → p2) ∧ p1)) ∧ (p5 ∨ p4)) → (p2 ∨ ((p2 ∨ True) ∧ (p2 ∧ (p1 ∧ p3)))))) ∨ p2) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h9 : ((p1 ∧ p3) ∨ p1) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h10 := h6 h9
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h12 : ((p1 ∧ p3) ∨ p1) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h13 := h6 h12
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185436937222347264772369034356 : ((False ∨ ((p3 ∧ ((False ∧ (True → p2)) ∧ p3)) ∨ (True → False))) ∨ (True → ((p2 → ((p4 ∨ p2) ∧ False)) ∨ (((p4 → False) ∧ p4) → p1)))) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39778960883140647199079386737 : (((True → (False ∨ ((((p2 ∨ p5) → False) ∧ (p3 → p5)) ∧ ((((((p4 ∧ p3) → p4) ∧ p1) ∧ (p4 → True)) ∨ p1) ∧ True)))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115213739881183524926938828823 : (((p3 ∨ (p2 ∨ (p1 ∨ (((p1 → p1) ∨ True) ∧ False)))) ∧ ((((((p4 → True) → False) ∧ p1) ∨ p2) ∨ p5) → (p5 → p3))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205201069802699470055750770059 : (((p2 → (True ∧ True)) ∧ (p5 ∨ p5)) ∨ ((p2 → ((p1 ∨ (p2 ∨ p1)) → ((p1 → ((p1 → False) ∨ True)) ∧ ((False → p3) → True)))) ∨ False)) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
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
  -- Implications on the right can always be decomposed.
  intro h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245648199671629256327080670800 : ((p3 ∧ p1) ∨ (((p3 ∨ (p2 ∨ p5)) → (p3 ∧ ((True ∨ ((p1 ∧ p5) → False)) ∧ ((p2 ∧ (p2 ∨ (p1 → False))) → (p5 → p3))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_26872253600414563396096441113 : (((p2 ∨ p1) ∨ (((p5 ∨ (((p4 ∧ p5) ∧ (((p3 ∨ p2) ∧ (True ∨ True)) ∨ p1)) ∧ p4)) ∧ ((p3 ∧ p4) ∧ p1)) → (False ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h3.left
          let h22 := h3.right
          -- Conjunctions on the left can always be decomposed.
          let h23 := h21.left
          let h24 := h21.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h3.left
          let h27 := h3.right
          -- Conjunctions on the left can always be decomposed.
          let h28 := h26.left
          let h29 := h26.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h31 =>
          -- Conjunctions on the left can always be decomposed.
          let h32 := h3.left
          let h33 := h3.right
          -- Conjunctions on the left can always be decomposed.
          let h34 := h32.left
          let h35 := h32.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h36 =>
          -- Conjunctions on the left can always be decomposed.
          let h37 := h3.left
          let h38 := h3.right
          -- Conjunctions on the left can always be decomposed.
          let h39 := h37.left
          let h40 := h37.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h41 =>
      -- Conjunctions on the left can always be decomposed.
      let h42 := h3.left
      let h43 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h44 := h42.left
      let h45 := h42.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57213897523035889291758998259 : ((((p1 → p5) ∨ p4) ∨ ((((p4 ∧ p4) → (p5 → False)) → p2) → ((p4 ∨ (p5 → ((((p1 ∨ False) ∧ p5) → p3) ∧ p4))) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224894081991131514431959642433 : ((p5 → (True ∨ p1)) ∧ ((p5 ∧ p5) ∨ (p1 ∨ (((p3 ∧ ((p4 → p1) ∧ p5)) ∨ (p1 ∧ (True → ((True ∧ True) → (True ∨ p5))))) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_190186188953663163947997741857 : (((False ∨ (((p5 ∧ p3) ∨ (p5 → p3)) ∧ p1)) ∧ p3) ∨ (((True ∧ False) ∧ (False ∨ (((False ∧ False) → True) ∧ (False ∨ (p1 → True))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175379153830204714824570830932 : ((True → ((p5 → ((((p2 ∨ True) → False) ∨ p3) → False)) ∧ (p4 ∧ (False ∨ p4)))) → (p1 ∨ (((True ∨ (p2 → (p4 ∧ p2))) → False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42164930406938628976735078630 : ((((p4 → p1) → (p1 ∧ (p1 ∧ (p2 ∨ (((p5 → (p2 ∨ p5)) → (((p1 ∧ p2) → (False ∨ p4)) ∨ p5)) ∨ (p3 ∧ p5)))))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803185854246081234586611269848 : (((p3 → (((True → (((((p1 ∧ True) ∨ p5) ∨ ((True → ((p5 → p3) ∧ False)) ∧ (False → (p3 → p4)))) → p1) ∨ p3)) ∧ p5) ∨ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_519853990564925288930652045296 : ((((p2 ∨ p1) → ((p4 → ((((p1 ∨ ((p5 ∨ p4) → True)) → p3) ∨ False) ∨ ((True ∧ False) → (p1 ∨ (p2 ∧ p1))))) ∧ (p1 → True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327062369964655731793452444967 : (True → ((((p3 ∨ (False ∨ p1)) ∨ True) ∧ (((False ∨ p2) → ((p3 → p5) ∨ (p4 ∧ (p5 ∨ (((p4 ∨ False) ∨ True) ∧ p3))))) ∧ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42703011282159170612712312955 : (((p5 ∨ (((((p3 ∧ p2) ∧ p4) ∨ (p5 → p1)) ∧ True) ∨ (p5 → (((p3 ∧ False) ∨ ((True ∨ (p3 ∧ p1)) → True)) ∨ p3)))) ∨ p1) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214395353986939573126195409501 : (((False → (p1 ∨ p4)) → p4) ∨ (((p1 → False) → p2) → (p2 ∨ ((p5 ∨ p1) ∨ (((True ∧ (False → (p3 ∨ p5))) ∧ p2) ∨ (True ∨ True)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150244690672635250925582871858 : ((p3 → ((p2 ∧ ((p5 ∧ ((False ∨ True) ∧ p4)) → (((p5 ∨ (p1 ∧ (p3 ∨ False))) ∧ p2) ∨ p1))) → p4)) ∨ ((False → p4) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205876791907680624148955828186 : ((True ∧ (((p2 → p4) → p3) ∨ p2)) ∨ ((True ∨ ((True ∨ p2) ∨ p5)) → ((((p2 → (((p3 ∨ True) ∨ True) ∨ p5)) ∨ p3) → False) ∨ True))) := by
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
theorem thm_5_vars_248823821095734652953999767154 : ((p3 ∨ p4) ∨ (((((p3 ∨ (p3 ∧ p3)) → (p4 ∨ p2)) → (False ∧ p4)) ∧ ((True → False) ∧ False)) ∨ ((False ∧ (p5 → p5)) → (p5 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223509340362764737909787600101 : ((False ∨ (p5 ∨ True)) ∧ (p2 ∨ (True → ((p2 ∨ (p4 ∧ False)) → ((p3 ∧ ((p5 → (p3 → p3)) ∨ p4)) ∨ ((p4 → (p5 ∧ True)) ∨ p2)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234620014331360135866946019089 : ((p3 → (False → True)) → ((((False ∧ (False → p3)) ∧ ((False ∨ (p5 → p4)) ∨ (((p4 ∧ (True ∧ False)) → (p3 → p4)) ∨ True))) ∨ True) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621430133931301313247975520202 : ((((True ∧ (p4 → (True ∧ ((p1 ∧ ((p1 ∨ p2) ∧ (((p2 ∨ (p5 ∨ (False → p1))) ∧ ((False ∨ p5) ∧ p4)) ∧ False))) ∧ True)))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253983922500475829360938600098 : ((p1 ∧ p5) → (((((p4 → False) → ((False ∨ p4) ∨ ((p4 ∨ p2) ∨ (p2 ∧ (True → p4))))) ∧ False) ∨ True) ∨ ((p2 ∨ p2) ∨ (p2 → p2)))) := by
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
theorem thm_5_vars_623041555634486582862775040324 : ((((p5 ∧ (False ∨ (((((p4 → ((p2 ∨ p5) → p1)) ∧ (p3 ∨ p4)) ∧ (True ∧ p4)) ∨ ((p2 ∧ False) → p2)) → (p4 ∧ p3)))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_45230583568452772189048405637 : (((p1 ∧ (((((((p5 ∨ (p1 → ((p3 ∨ p4) ∧ p4))) → p1) ∧ p3) ∧ p1) → p2) → (p4 → (p2 → (False ∧ p2)))) ∨ p3)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322213893630598056003516642203 : (p5 ∨ ((((p3 → ((((p2 ∨ ((True → p4) ∨ p5)) ∨ p1) ∧ (p1 → p2)) ∨ p3)) ∧ (p3 ∨ (True ∨ ((False ∧ p4) ∧ p2)))) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357237403480226271585085427218 : (p5 → ((p4 → p4) ∧ (((False ∧ False) → p4) → ((p4 → (((p1 ∨ False) → ((False ∨ False) ∨ (p2 ∧ True))) ∨ (p3 ∧ p2))) ∨ (p3 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159045263908003045454669258313 : ((p5 ∨ (((True ∨ (p2 ∨ (p5 ∨ p2))) → ((True → (((p3 ∨ p5) → True) ∧ False)) → p4)) ∨ p5)) ∨ (((p1 ∨ False) ∨ True) ∨ (p1 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199126356598180208758578950697 : ((((True ∨ (p1 ∧ p5)) → (p5 ∧ False)) ∧ True) → ((False → p4) → (((p1 ∨ True) ∨ ((False ∨ True) ∨ (p1 → True))) → ((p4 → p1) ∨ p1)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h1.left
      let h7 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h1.left
      let h10 := h1.right
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h11 : (True ∨ (p1 ∧ p5)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h12 := h9 h11
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h1.left
        let h19 := h1.right
        -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
        have h20 : (True ∨ (p1 ∧ p5)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h18, we can now drive its conclusion.
        let h21 := h18 h20
        -- We need to get the right conjuct of h21 based on <expert-advice>.
        let h22 := h21.right
        -- False on the left can always be used.
        apply False.elim h22
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h1.left
      let h25 := h1.right
      -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
      have h26 : (True ∨ (p1 ∧ p5)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h24, we can now drive its conclusion.
      let h27 := h24 h26
      -- We need to get the right conjuct of h27 based on <expert-advice>.
      let h28 := h27.right
      -- False on the left can always be used.
      apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622776324532412036814372790343 : ((((p4 ∧ (p3 ∨ ((((False ∨ p1) → p4) ∨ ((p2 ∧ ((((p4 ∧ p4) ∧ True) ∨ ((p5 → p3) → p3)) ∧ p5)) ∨ p3)) ∨ p4))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_69145967472523341845115519576 : ((p5 → ((((((p4 ∨ p3) → (p1 → p2)) → ((p1 ∨ ((False ∧ p2) ∨ p1)) → True)) → (p4 ∨ p1)) ∧ p5) → ((p3 ∨ p4) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60392356275082368290277543046 : (((p3 → p4) → ((((((p2 ∨ p1) ∧ ((p4 ∨ p1) ∨ p3)) ∧ p1) ∧ (False ∧ (p4 ∨ p3))) ∧ False) ∨ ((True ∧ (p5 → p5)) ∨ p3))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299382749277700224221186755234 : (False ∨ (((p2 ∨ p4) → (((p4 ∨ ((p4 ∧ (p4 ∨ p4)) ∨ p5)) ∧ ((True ∧ (p2 ∧ (p2 ∨ p1))) ∧ (p3 ∧ (True ∨ p1)))) ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701881357762990348021985815909 : ((((False ∨ ((((p5 ∨ p1) ∧ p4) ∨ (True ∨ p3)) ∧ p2)) ∧ ((False ∧ ((p3 ∧ p2) ∧ (p2 ∨ p5))) ∨ (p2 ∨ ((p1 → False) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659085554730097581893069343682 : ((((p2 → (((False ∨ p2) → p1) ∧ (p1 → (p1 → (p5 ∨ (p4 ∧ (p1 → (((p3 ∨ p3) → p5) ∧ (p2 → p4))))))))) ∨ (p4 → p4)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_232223014365229179460236075791 : (((p1 → False) → p4) → ((p4 ∨ ((True → p1) ∧ (p4 → ((((p4 ∨ ((False ∨ p5) ∨ p5)) → ((p5 ∨ p2) ∧ True)) ∧ False) ∨ p4)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137751439740315870674652255139 : ((p2 ∨ ((((True ∨ p1) → ((p1 → (p5 ∧ p4)) ∧ p5)) ∧ ((p4 → (p2 ∨ p3)) ∧ ((False ∨ False) ∨ p4))) ∨ True)) ∨ (p1 ∧ (p1 → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52396172846600337416830982709 : (((((p4 → p5) ∨ (p1 ∨ p2)) ∧ ((((p2 ∨ p5) ∧ p1) ∧ p3) ∨ False)) ∧ (False ∧ (p3 ∨ (((p2 ∨ False) → p4) ∧ (True → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135267725120255860405224614880 : (((True ∨ (p3 ∨ ((((((True → p1) → (p1 ∨ True)) ∨ p1) → False) → (p3 ∨ (p1 → p5))) ∨ True))) → (True → False)) ∨ ((False ∨ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345550920571881503421168006732 : (p3 → (((((p4 ∨ (p5 ∨ p3)) → False) → p2) → ((p2 → ((p2 ∨ ((p2 → p5) → ((p4 → p4) ∧ True))) ∧ (False ∨ p2))) ∧ True)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118459312350909030470076132025 : ((p3 ∨ (((((False → True) ∨ (p4 ∨ p1)) ∨ p2) → ((False ∧ ((False ∧ (True → True)) ∧ p3)) ∧ ((False ∧ p1) ∧ p5))) ∨ p5)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730316950366282622775249515999 : (((((p4 → p5) → p2) → (((p5 ∧ (p4 → ((p4 ∨ (((p4 ∧ ((p3 ∧ True) ∧ True)) ∨ p4) ∧ p4)) ∧ (True ∨ p1)))) → p5) ∨ False)) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351940561192299591768500051478 : (p4 → (((p5 ∨ (p1 ∨ False)) ∧ (False ∨ ((p5 ∧ p3) ∨ p5))) → ((((p2 ∨ (p2 → (p1 ∨ p1))) ∨ ((p2 ∨ p4) → p1)) ∨ True) ∨ p5))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h14 =>
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h19
    case inr h20 =>
      -- False on the left can always be used.
      apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1493465448573001326958212818 : (((p1 ∧ (((p2 ∨ p3) ∨ p5) ∧ (True ∧ ((p1 → ((p2 ∧ (False ∨ p3)) → False)) → (p3 ∧ p4))))) ∨ (p3 → p3)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309657778102684663270073146076 : (p2 ∨ ((True → ((p1 ∨ ((True ∧ ((p1 → (((p3 ∧ False) ∨ ((True ∧ True) ∧ True)) ∨ p5)) → p4)) ∧ p2)) ∧ p1)) ∨ ((p5 ∧ p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171550688863203308180068870282 : (((((p3 → (((p3 → (p5 ∨ p2)) ∨ (p2 → p1)) ∨ True)) → True) → False) ∨ p5) ∨ (p3 ∨ (p5 ∨ (p1 → ((False ∨ True) ∨ (p4 ∧ False)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185058055500152953538707941226 : (((False ∧ p5) ∨ ((p5 ∧ p4) ∧ (p4 ∨ (False → (p3 → False))))) ∨ ((((True ∨ p2) → p3) ∨ (p3 ∨ p2)) ∨ (False ∨ ((p5 ∧ p2) → p5)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357895362736340289293687065583 : (p5 → (p5 ∧ (False ∨ ((((((p1 ∧ p5) ∨ p5) ∨ False) ∨ p2) ∧ (p3 ∨ p1)) ∨ ((True ∧ (True → p1)) → ((p3 ∨ (p3 → p4)) ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637881490063508882293781251762 : ((((((False → (p3 ∨ True)) ∨ ((True → p1) → p3)) ∧ (True → (True → (p2 ∧ (((p4 → (True ∨ p4)) ∧ p3) → (False ∧ True)))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355916414374968205079090143456 : (p5 → (((p3 ∨ (((p5 ∨ (((False → p5) → False) → (p2 → ((p2 ∨ p4) ∨ True)))) ∧ p4) ∨ p4)) ∨ (p3 → p4)) → ((p2 ∨ True) ∨ p4))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h8
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
  case inr h12 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190581276479232024113731980072 : ((((p1 ∧ (p3 ∧ p5)) → ((True ∨ p1) ∨ False)) → p5) ∨ ((True ∨ (p4 ∧ True)) ∨ (True ∨ (p1 ∧ ((((False ∧ True) → False) ∧ p3) ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309308986328033428746404083500 : (p2 ∨ (((((p3 ∨ ((((p2 ∧ p3) ∧ p5) → (((p4 ∨ p2) ∨ p4) ∧ (p4 → p5))) ∨ False)) → (p5 ∧ True)) → p1) ∨ p5) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337853464594116118086267974674 : (p1 → (((False ∨ ((p4 ∨ (p1 → ((p3 ∧ p2) ∨ False))) ∧ (p5 → p1))) ∨ p1) ∨ ((p4 ∧ ((p4 ∨ p2) → (p2 ∧ True))) ∧ (p5 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797898442184963498294000347542 : (((p1 → ((p2 ∧ (False ∧ (((p1 → ((p3 ∨ ((p1 ∧ p3) → p2)) ∧ (True → p3))) → (p5 → (True → False))) ∧ p1))) ∨ (True ∨ False))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_216690418710698941566396267464 : ((((p5 → True) ∨ p4) ∧ p5) → (((True → (p3 → p1)) ∨ (False ∨ ((p2 ∨ (p5 ∨ (True ∧ ((True ∧ p4) ∨ p3)))) ∧ p1))) ∨ (True ∨ True))) := by
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
theorem thm_5_vars_195175731200623292863371427366 : ((((p2 ∧ (p3 ∧ p3)) ∧ p2) ∨ (p4 → p4)) ∧ (p5 → (p3 ∨ ((True ∨ (True → False)) ∨ (p5 → (((False ∨ (p5 ∨ p1)) ∨ p2) ∧ True)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611136699460785825928951592032 : ((((((True ∧ (p4 → False)) ∧ (True → ((True ∨ (True ∨ ((p3 → p3) ∧ p5))) ∧ (((p4 → p1) → p5) ∧ (p5 ∧ p3))))) → p2) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_60669442432522876363555877517 : ((True ∧ ((p1 ∧ ((p1 ∧ ((p2 ∨ (False → False)) → (((False → p3) ∨ p4) ∧ True))) → p5)) ∨ ((p5 → ((p5 → p5) ∨ p4)) ∨ p2))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218916793053740235256969630456 : ((p3 ∧ ((True → p5) → p4)) → (p3 ∧ (((True → False) ∨ (p4 ∧ ((p3 ∨ True) → (((p3 ∨ p3) ∧ p4) ∧ False)))) ∨ (True ∨ (True ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264072102299043881748303465890 : (True ∧ ((((p2 ∨ p3) ∧ False) ∧ ((p5 ∨ (p3 ∧ p3)) ∨ p5)) ∨ (True ∨ ((((p3 ∨ (((True ∨ p5) ∧ False) → p1)) ∧ p2) → p1) → p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49662980527281209727584098895 : ((((False ∧ (p4 → False)) ∨ ((False ∨ ((False → (p5 → ((False ∧ p5) ∧ (True → False)))) ∧ (p1 → p4))) → p2)) → ((p4 → p4) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729104095705442436993928705476 : (((((True → p4) ∧ p1) → ((((p1 ∧ (False → False)) → p5) ∨ ((((p3 ∨ True) ∨ (p1 ∨ p2)) ∧ p3) ∧ (p4 ∨ (p5 ∨ False)))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619054471718661403269792270456 : ((((((p1 ∨ p5) → p2) ∨ ((((p5 ∧ ((p2 ∧ (((p5 ∨ (True ∧ (p3 → p4))) ∨ p5) ∧ p3)) ∧ p3)) ∧ False) ∧ p5) ∨ p2)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57029846342879172914480350770 : (((p1 → (p5 → True)) ∧ ((p1 → p5) → (((p1 ∨ (((False → False) ∧ p4) ∨ True)) ∧ p1) ∧ ((True → (True ∧ (True ∧ p5))) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116085563407193762966382645774 : ((((p5 ∧ p5) ∨ p4) ∧ (False ∨ (((((p3 ∧ (p2 ∧ ((True → p5) ∨ (False → p1)))) ∧ p2) ∧ (p1 → p2)) ∧ p2) → False))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205069727273823402415977219306 : (((p3 → (p2 → (p3 ∨ p4))) → False) ∨ ((False ∧ (True ∨ ((p2 → p2) ∧ (p4 ∧ p5)))) → ((p3 ∧ (True ∧ (p4 ∧ (False → True)))) ∨ p1))) := by
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
theorem thm_5_vars_723862052547425269158529573977 : (((((p5 → p5) → p1) ∧ (p3 → ((((p1 ∨ p2) ∨ p3) ∨ ((((p4 → ((p2 → True) ∧ True)) ∧ p2) ∧ True) ∨ (p2 ∨ p4))) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166171192614524744113409633754 : ((False ∧ (p3 ∧ (p3 ∧ (((False ∨ True) ∧ ((p1 ∧ (p5 ∧ p5)) ∨ p5)) ∧ (p1 ∧ True))))) ∨ ((p2 ∧ ((True → p5) ∧ (False ∧ False))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147228821954376251498357081587 : (((((((p2 ∧ (p5 → (((p1 ∨ p5) ∨ True) ∨ p3))) ∨ (False ∨ False)) ∧ (False ∧ p3)) ∧ p1) ∧ False) ∨ p3) ∨ ((False ∨ False) → (p3 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142348278082778503048279425249 : ((p3 ∧ ((True → False) ∧ ((p5 ∨ (True ∧ (False ∨ p5))) ∧ ((p4 ∨ p4) → (False ∨ ((p1 ∨ False) ∨ (p3 → p5))))))) → ((p4 ∧ p5) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h17 := h4 h16
      -- False on the left can always be used.
      apply False.elim h17
  -- Conjunctions on the left can always be decomposed.
  let h18 := h1.left
  let h19 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h19.left
  let h21 := h19.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h21.left
  let h23 := h21.right
  -- Disjunctions on the left can always be decomposed.
  cases h22
  case inl h24 =>
    -- One of the premise coincides with the conclusion.
    exact h24
  case inr h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- False on the left can always be used.
      apply False.elim h28
    case inr h29 =>
      -- One of the premise coincides with the conclusion.
      exact h29
  -- True on the right can always be proven directly.
  apply True.intro



