variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244543568818298229806089888478 : ((False ∧ p3) ∨ (p3 → (((p2 ∧ (p5 ∨ p1)) ∨ ((((p3 → p2) ∧ False) ∨ True) ∨ (False ∧ (((p3 ∨ p5) ∨ (p3 ∧ p3)) ∧ False)))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186787249859859929881762276612 : (((((False ∨ True) → p4) ∨ p3) ∧ (p3 → ((False → p3) ∧ p2))) → ((p5 → (p1 ∨ (True ∧ (((p1 ∧ p5) ∨ (p5 ∧ p3)) ∨ p4)))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_472436904330238716650226207651 : ((((p5 ∧ (False ∧ (p4 → (p2 ∨ (True ∧ (p5 → (p1 ∨ False))))))) ∨ ((True ∧ ((p4 → ((True → p5) → p3)) ∧ p5)) → (True → True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804912519829763167527263877801 : (((p3 → ((False ∨ p1) ∨ (((p2 → (p4 ∧ (p2 ∨ False))) → (p2 → ((p2 ∨ False) ∧ p4))) ∧ ((True → (p2 ∧ (p2 ∨ p1))) ∨ p3)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181338420661967996247958911172 : ((True ∨ (p2 → (p4 ∧ ((p4 ∨ ((p1 → p3) → True)) ∨ (p5 ∧ p2))))) → (((p5 ∧ (p3 ∨ (True ∧ (p5 ∨ (False ∨ True))))) → False) ∨ True)) := by
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
theorem thm_5_vars_257366891561732709085204857142 : ((p2 ∨ p5) → (((p1 ∧ (p5 → (p2 ∨ (((p1 → p3) ∧ p3) → (p4 → (True ∧ ((False ∨ (p5 ∨ p2)) ∨ (False → p2)))))))) → p2) ∨ True)) := by
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
theorem thm_5_vars_1810872240678137056142172592 : ((p5 ∧ (p2 → ((((p4 → p5) ∨ ((True → ((True ∨ (p4 → p4)) ∧ p2)) ∧ (p1 ∧ p3))) ∧ p5) ∧ p3))) ∨ (p4 → (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112734643434591182963596210182 : (((((p4 → ((p3 ∧ p3) → ((p5 → True) ∧ (True ∧ p4)))) → False) ∧ (p5 → (p2 → ((p3 ∧ p5) → (p3 ∨ p5))))) → p2) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179441871828218865070845380478 : ((p5 ∨ (((p3 ∧ (p2 ∧ (((p1 ∧ False) → p1) ∧ p1))) ∨ p3) ∨ True)) ∨ ((p2 ∨ (p5 → p2)) ∧ (p1 ∧ (p1 ∨ ((True → p2) ∧ p2))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60443819417502639175705417112 : (((p5 → True) → (((p4 ∨ p5) ∧ (p2 ∨ p5)) ∧ (((((p3 → p1) ∨ False) ∨ (True ∨ (p3 ∧ ((p4 ∧ p3) ∧ False)))) ∧ p2) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37354559005601775152211279414 : (((((((p5 ∧ (p3 ∨ (p1 ∧ (((False ∨ (p4 ∨ True)) ∧ p2) ∧ ((p4 → p3) ∨ p1))))) ∨ p5) ∧ (p4 → p1)) ∨ True) ∨ p2) ∧ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_677835932984020930190902004349 : ((((((p2 ∧ (p5 → False)) ∨ ((True ∧ (p5 ∨ ((False → p4) ∧ p5))) ∨ (False ∧ True))) ∧ (p2 ∧ True)) ∨ (p3 ∨ ((False → True) ∨ p4))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248657704153908125557208044191 : ((p3 ∨ p1) ∨ ((False ∨ p5) → (True ∧ (((((False ∧ (p4 ∨ ((p1 ∨ p4) ∨ (p2 → p5)))) → False) → ((True → p2) ∧ p4)) ∨ p3) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180185382368786647452253070256 : ((((p1 ∨ ((p4 ∧ p3) ∨ False)) ∨ ((p4 ∨ (p2 ∧ False)) ∨ True)) → p1) → ((((p3 → p5) → ((False ∧ (p5 ∧ True)) ∨ p5)) ∨ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118901165641313067555448656159 : ((True → (p4 ∨ ((((False ∨ p4) ∨ p2) ∨ (False → (True ∧ ((p4 ∨ p2) ∨ p1)))) → (False ∨ (((p5 → False) ∨ p1) ∨ p1))))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_923898777921623746664063318271 : (((((p2 ∨ p5) → (p3 ∧ (False ∧ ((p1 ∨ p4) ∨ (True ∧ p5))))) ∧ (((p1 → (p3 → True)) → ((p2 ∧ (p4 → p5)) → p4)) → p5)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p1 → (p3 → True)) → ((p2 ∧ (p4 → p5)) → p4)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : (p2 ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- False on the left can always be used.
    apply False.elim h12
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h13 := h3 h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h14 : (p2 ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h15 := h2 h14
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- We need to get the left conjuct of h16 based on <expert-advice>.
  let h17 := h16.left
  -- False on the left can always be used.
  apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747458438192880451777940976370 : ((((True → False) → ((p3 ∧ (p5 ∨ p3)) ∨ ((((p5 ∧ False) ∧ (p2 ∨ (((p5 ∧ p1) → p5) ∧ False))) → p5) ∧ ((p4 → p3) ∧ p5)))) ∨ p3) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133820465078316230838127422662 : ((((p4 ∧ p3) ∨ (((False → p5) ∨ ((True → (p2 ∨ ((p4 ∧ p5) ∨ p2))) → False)) → (p1 ∨ (p1 ∨ True)))) ∧ True) ∨ ((p5 → p5) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40404209267788855705423108544 : (((((p1 → ((p5 → (p4 → (True → (p2 ∨ p1)))) ∧ (((False → True) → (p4 → False)) ∧ p2))) ∨ ((True ∨ p5) ∧ p5)) ∨ True) ∨ p2) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255970441231913547793754697777 : ((True ∨ p3) → ((((p3 → (((True ∧ (p4 ∧ (p4 → ((p4 → p3) → p4)))) ∧ p2) ∨ False)) ∧ (p3 ∧ (p3 → True))) ∨ (p1 ∨ True)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165196186331342970962277093766 : (((((False ∧ ((p2 ∨ False) ∨ ((True → (p5 ∧ False)) ∧ False))) ∧ p1) ∨ True) ∨ (False ∨ p3)) ∨ ((p4 ∨ (p5 ∨ (p1 ∨ p4))) ∨ (p3 ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144825985533103066773285470199 : ((((p1 ∧ ((False → (False ∨ p1)) → True)) ∨ ((p2 ∧ p4) ∨ ((p2 → p2) ∧ True))) → ((p2 ∨ True) ∨ p3)) ∧ (((False ∨ p1) ∨ False) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138246979322757750398225200642 : ((p2 → ((True → (p4 ∧ p4)) → ((p3 → (p2 → (((p2 → False) ∨ p3) → (p2 ∨ p2)))) ∧ (p1 ∨ (p5 → p1))))) ∨ ((p3 → p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68542166112003214284639926465 : ((p3 → (p3 → ((p2 ∨ ((p2 ∨ False) → ((True ∧ (p3 ∧ ((False ∨ (p5 ∧ (p3 → p5))) → p1))) → (p3 ∨ p5)))) → (p5 ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_15211614392965265746231522699 : (((p1 → (((False ∧ (False ∨ p1)) ∨ (p2 → ((False ∧ (p2 ∨ p1)) ∧ ((True ∧ ((False → p4) ∧ p2)) → False)))) ∨ True)) ∨ (p5 ∧ True)) ∧ True) := by
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
theorem thm_5_vars_215061800890592334309370748061 : (((p4 ∨ p5) → (p3 ∨ p4)) ∨ ((((p4 → (p5 → False)) ∨ p1) ∨ (((p4 ∧ p4) ∧ (True ∧ p3)) → (((p5 → p3) ∨ p1) ∧ p4))) ∨ p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h8
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h10.left
  let h14 := h10.right
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147028141124332634434364431181 : (((((True ∨ (((p1 → p1) ∨ p2) → ((p5 ∨ (p5 ∧ p5)) ∧ p3))) → p2) ∨ (p4 ∧ (p4 ∧ False))) ∧ p4) ∨ (True ∨ ((p4 ∨ False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83243133024719996957292536353 : (((((((False → (p4 ∨ False)) ∨ (True → p4)) → ((p1 ∨ p5) → True)) ∨ (p1 ∨ p1)) → p4) ∧ (((p5 ∧ False) → p5) ∧ (False → p3))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : ((((False → (p4 ∨ False)) ∨ (True → p4)) → ((p1 ∨ p5) → True)) ∨ (p1 ∨ p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h6
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165884223212682681661137077698 : ((((True → True) ∨ True) → ((p5 → p3) ∧ ((p4 ∧ (((p1 ∧ p2) → True) ∨ p3)) → p2))) ∨ ((p5 ∨ True) → (True ∨ ((p2 ∧ True) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318730583846231464442067117855 : (p4 ∨ ((((p3 → p1) ∨ p2) ∧ (p1 ∧ ((((True ∨ (((p4 → True) → True) ∨ (p3 ∧ p1))) ∧ False) ∨ (p2 ∨ p1)) → False))) → (p3 ∧ p3))) := by
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
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (((True ∨ (((p4 → True) → True) ∨ (p3 ∧ p1))) ∧ False) ∨ (p2 ∨ p1)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : (((True ∨ (((p4 → True) → True) ∨ (p3 ∧ p1))) ∧ False) ∨ (p2 ∨ p1)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- False on the left can always be used.
    apply False.elim h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h19 : (((True ∨ (((p4 → True) → True) ∨ (p3 ∧ p1))) ∧ False) ∨ (p2 ∨ p1)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h20 := h18 h19
    -- False on the left can always be used.
    apply False.elim h20
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h15.left
    let h23 := h15.right
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h24 : (((True ∨ (((p4 → True) → True) ∨ (p3 ∧ p1))) ∧ False) ∨ (p2 ∨ p1)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h21
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h25 := h23 h24
    -- False on the left can always be used.
    apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54733458648666055532662871343 : ((((p1 ∨ (p5 ∧ p4)) ∨ (p4 → (p5 ∧ p1))) → (p4 ∧ ((p4 ∨ p1) ∧ ((True ∨ (((False → False) → p3) → (p3 ∧ p5))) ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49188532478589980818040624005 : ((((p1 → (p5 → (False → p1))) → ((p5 → True) → (p4 ∧ ((True → (((p2 → False) → p2) ∧ p2)) ∧ p5)))) ∨ (True ∨ (p3 ∧ p1))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62404636722816093875764083727 : ((p3 ∧ ((p2 ∨ (p2 ∧ ((True → (p4 ∧ False)) ∧ p1))) ∧ (p2 ∨ (p1 → ((True ∨ (((False ∨ p3) ∧ p1) ∨ p5)) ∨ (p3 → True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185064464963397756632900539502 : (((p2 ∧ p5) ∨ ((p2 → False) → (p5 ∧ ((False ∧ p4) ∧ p1)))) ∨ (True ∨ ((p3 ∨ ((False ∨ p1) ∨ (p4 ∧ ((p1 ∧ False) → p1)))) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200439274672122960869342945195 : (((p4 ∨ p4) ∨ (((p2 ∧ p4) → p5) ∨ p1)) → ((((p5 ∨ p3) → False) ∧ (p1 ∨ p5)) ∨ (False → (p3 ∧ ((p2 ∨ p5) ∧ (True → p1)))))) := by
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h4
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h4
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h7
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h11
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- False on the left can always be used.
      apply False.elim h11
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h14
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h14
      -- Implications on the right can always be decomposed.
      intro h15
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118220123475043974515125539736 : ((p1 ∨ (((True → (((p2 ∨ (p1 ∧ (p5 ∨ (p5 → (p4 → (p4 ∧ p1)))))) → (p5 → (True ∧ p3))) ∨ p5)) → p5) ∨ p4)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114515634256206509985517573232 : ((((p5 → p1) → (((True → p5) ∧ (False ∨ p5)) ∧ ((p1 ∨ ((p2 ∧ p2) ∧ p2)) → p1))) → (((p5 ∨ p5) ∨ p1) → p4)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166934354223271849287379228346 : ((((False ∨ (True ∧ p2)) → (((p5 ∧ False) ∨ (p5 ∨ p3)) ∧ (p4 ∧ (False → p1)))) ∧ p4) → (((p3 → p1) ∨ (p3 → p5)) ∨ (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3283254852195386298007206086 : ((p4 → p3) ∨ (((p2 → (p3 ∨ (p2 ∧ (p3 ∨ (p5 → ((p3 → True) ∨ ((p5 → p1) ∨ p1))))))) → ((p3 → p4) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214682094103992959096202104079 : (((p5 → p2) ∧ (False ∨ False)) ∨ (p5 → (((((True ∧ (p3 ∨ False)) ∧ p2) ∨ (p4 ∧ p5)) ∨ (p1 ∨ (p4 → p3))) ∨ ((p3 ∨ p2) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734536937445381892546821342435 : ((((p1 ∨ p1) ∧ (((((((p4 ∨ True) ∨ (p3 → True)) ∧ True) ∧ p5) → p5) ∨ (p4 → (True ∨ (p1 ∨ (p3 ∧ p3))))) → (False ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252653748881560503128754698184 : ((p5 → p4) ∨ ((((p3 ∨ ((p2 ∨ p5) ∨ (p5 → p3))) ∧ p2) ∨ True) ∨ ((p1 → ((p5 ∨ False) ∨ p1)) ∧ (p5 → (False ∨ (p4 → False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158931556472860400464170625409 : ((p2 ∨ (((((((p3 ∧ p3) → False) ∨ p4) ∧ (True ∧ (False → (True ∨ p4)))) → p5) ∨ p2) ∨ True)) ∨ ((p4 ∨ (p2 ∧ p1)) ∧ (p3 ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258672542621497893707320012439 : ((p5 ∨ p5) → (((p4 ∧ p4) ∧ p3) ∨ (p4 ∨ ((((((False → True) ∧ False) ∧ (p4 ∧ (p2 → (p1 → (False ∨ p2))))) ∧ p5) ∨ True) ∨ p4)))) := by
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
theorem thm_5_vars_42057566312228803845337635380 : ((((p3 ∨ False) ∨ ((p1 → (p3 ∧ (True ∨ ((p5 ∧ (p5 ∨ ((False ∧ ((p1 ∧ p1) ∧ p2)) → (p5 ∨ True)))) ∧ True)))) ∨ p4)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696731476297341448862398370633 : (((((((True ∧ ((p4 ∨ True) ∧ True)) → (p1 ∨ p3)) → p4) → p3) ∧ ((True ∨ (p3 ∧ p4)) ∨ (False ∨ (p4 → (p5 → (p4 ∧ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40686812834459335038182276337 : (((((p4 ∨ (p5 ∧ ((p1 → ((p5 → ((p2 → True) → (p5 ∨ p2))) → False)) ∨ p4))) ∧ (p3 → (p4 ∧ (p2 ∨ p4)))) → p5) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55159400197671427475989278793 : ((((p3 ∧ ((p4 → p4) ∧ False)) ∨ False) ∨ ((((False ∨ p1) ∧ p3) ∧ p4) ∨ ((p3 ∨ ((True ∧ p1) ∨ p3)) ∧ ((True → p4) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752424147838850303991731725280 : (((False ∧ (((p2 ∨ (((((p3 ∨ p4) → (p2 → (p4 → p5))) → False) ∧ p4) ∧ p5)) ∨ ((p2 ∨ (p3 ∧ (p5 ∧ True))) → p5)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214822074079408348909344144861 : (((p4 ∨ False) ∨ (p5 ∧ p1)) ∨ (((False ∨ p4) → ((p3 ∨ (p4 → (True → p3))) ∨ ((p4 ∧ (p4 ∨ (p3 ∨ (False → p5)))) ∨ p2))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643071677101845276311602206477 : ((((p2 ∧ (False → ((p5 ∧ (p5 ∨ ((False ∨ False) → p4))) ∨ (((p4 ∧ p4) ∨ (p4 → p1)) → (p4 ∨ (p1 → (True ∧ True))))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117274134560974550869479152460 : ((False ∧ ((((p5 ∨ p5) ∧ ((((((True → (p3 → (True ∧ p3))) ∨ True) → (p1 → p3)) ∨ True) → True) ∧ False)) ∨ p2) ∨ p3)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194179429895694607860256591201 : ((p2 → ((True ∧ True) ∨ (p3 ∧ (p4 → (p4 ∧ p5))))) → (((((p1 ∧ p3) ∧ (p4 → p4)) ∨ (p5 ∧ (True ∨ p4))) ∧ (False ∧ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765491335765910836069652545160 : (((p4 ∧ (((p3 ∧ (True ∨ (True ∨ (p2 ∨ (p5 ∧ (p4 ∨ ((p1 → p2) ∧ p5))))))) → False) ∧ ((((True → True) → True) ∧ p3) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207066261649059286198597969723 : (((p2 ∧ ((p2 ∨ p3) → p3)) ∧ p4) → (((((p5 ∨ True) ∨ p4) ∧ ((p2 ∧ p4) ∧ (((False → p2) → p3) → p2))) ∧ True) → (False ∨ p3))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h6.left
      let h10 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h1.left
      let h14 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h17 : (p2 ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h18 := h16 h17
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h6.left
      let h21 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h20.left
      let h23 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h1.left
      let h25 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h24.left
      let h27 := h24.right
      -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
      have h28 : (p2 ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h26
      -- We have shown the premise of h27, we can now drive its conclusion.
      let h29 := h27 h28
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h29
  case inr h30 =>
    -- Conjunctions on the left can always be decomposed.
    let h31 := h6.left
    let h32 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h33 := h31.left
    let h34 := h31.right
    -- Conjunctions on the left can always be decomposed.
    let h35 := h1.left
    let h36 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h37 := h35.left
    let h38 := h35.right
    -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
    have h39 : (p2 ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h37
    -- We have shown the premise of h38, we can now drive its conclusion.
    let h40 := h38 h39
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h40



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63949863379790741021982247039 : ((False ∨ ((p1 ∧ (((False ∧ (p3 ∨ p4)) ∨ ((p5 → True) ∨ (False ∨ p5))) → (p1 → ((p4 ∨ p1) ∨ ((p4 → p3) ∨ False))))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679376772625691058661527854846 : ((((p4 → ((p2 ∧ (True ∧ ((p3 ∧ p1) ∨ (p4 → (((p1 ∨ (p5 ∨ p4)) ∧ p2) ∧ p1))))) ∨ p1)) ∨ (((True → False) → p4) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179192378276821099728104966765 : ((p3 ∧ ((p3 → (False ∧ p2)) → (p1 ∧ (p1 ∧ ((p5 → True) ∨ p3))))) ∨ (True → (True ∨ (True ∧ (((p4 ∧ p3) ∨ (p1 ∨ p1)) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157662806869867567069043919635 : ((((p2 → ((True ∨ p3) → ((True ∨ True) ∨ (False ∨ p1)))) ∧ (p1 ∧ False)) ∨ (p2 ∨ (p5 ∨ p3))) ∨ ((p1 ∧ ((p2 ∧ False) ∧ p5)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352793119773522437814902616832 : (p4 → ((p1 ∨ p3) → ((p4 ∧ ((p2 ∨ ((p3 → (False → p3)) → (p1 ∧ ((p3 ∧ True) ∨ ((p3 ∨ p1) ∨ (p1 ∨ p2)))))) ∧ p3)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41648328947013697638304052583 : (((((p4 → (True ∨ (p4 ∨ p3))) → p2) ∧ (p3 ∧ ((p1 ∧ True) ∧ (((p1 ∨ p1) ∧ (p5 → ((p3 ∧ False) ∧ p3))) ∧ False)))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114638308870281354728590592454 : (((((p4 → p5) ∨ (((p2 → (p2 → True)) → True) → ((p5 → False) → p5))) → p1) ∨ (((p3 ∨ (p1 → p4)) ∨ p2) ∨ True)) ∨ (p1 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160881295628255667047031267084 : ((((p4 ∨ (p5 → p5)) ∨ p3) ∨ (((False ∧ (p4 ∨ p3)) → p5) ∧ (((False ∧ p2) ∧ True) → p4))) → ((p3 ∧ (p3 ∧ (p3 → p4))) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139454957274082829717898918939 : (((((p2 → ((((p1 ∨ (p2 ∨ p3)) → p5) → (p3 ∧ p3)) ∨ (p3 ∨ (p1 → p2)))) → (p3 ∧ p3)) ∨ True) → p3) → ((p3 ∨ p5) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 → ((((p1 ∨ (p2 ∨ p3)) → p5) → (p3 ∧ p3)) ∨ (p3 ∨ (p1 → p2)))) → (p3 ∧ p3)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667900492609122306589212984729 : ((((p2 ∨ ((((False → (p3 ∧ p3)) → ((((p2 ∨ (p3 ∨ True)) ∧ False) ∧ False) ∧ p5)) ∨ (p1 ∨ False)) ∨ p1)) ∧ ((True ∧ p4) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48077613676003186708130202995 : (((((p5 ∨ (p4 → (p3 ∧ p5))) ∧ True) ∨ (((True ∨ p3) → (((True → (p3 ∨ p2)) ∨ p2) ∨ p4)) → (p2 → p4))) → (p3 ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318851611619516193927645528682 : (p4 ∨ ((((((((p1 ∧ p2) ∧ p5) ∧ p3) ∨ (p2 → p2)) → (p4 → (((p2 → p1) → False) → False))) → p5) ∨ True) ∨ ((p4 ∨ p5) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42380157153666117656487469118 : (((p4 ∧ (((p1 ∨ (((p4 ∨ False) ∧ ((p3 ∧ (p2 ∨ False)) → p1)) ∨ p3)) ∨ (p2 ∧ (p1 ∧ (False ∧ False)))) ∨ (True → False))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616393766803135157413531463978 : ((((((True ∧ ((True ∨ True) → ((p3 ∧ (p2 ∧ False)) → p4))) ∧ p2) → (p3 ∨ ((False ∨ ((p3 ∨ p4) ∨ p2)) ∧ (p4 ∧ p3)))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_260941853441952738222405657792 : ((p4 → False) → (p4 → (True ∧ (p2 ∨ ((True → (((p3 ∨ (p1 ∧ p1)) → p4) ∧ ((False ∧ p1) → (p3 ∧ ((p2 ∨ p2) ∧ p4))))) → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691942796261652896449196992263 : ((((p3 → (p1 → (((False ∨ (p4 ∨ p5)) ∨ (((p3 ∨ p1) ∨ p3) ∨ p2)) ∨ p3))) → (((((p3 → p1) → True) → False) → p1) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792929424841870325512683041729 : (((True → ((True ∨ p2) ∧ (p3 ∨ (((False ∨ (p4 ∨ ((p1 → p4) ∨ True))) ∧ (p3 → (p2 ∨ p5))) ∨ (False → (False → (p3 ∨ True))))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39002475293599199201696202739 : ((((p2 ∨ p3) ∧ ((((p5 → p5) → (p5 → ((True ∨ (p4 → p5)) → ((p1 ∧ ((p5 → p3) ∧ p1)) ∨ True)))) ∨ True) ∧ p4)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321173071231187884996311408881 : (p4 ∨ (p3 ∨ (((p4 ∨ (True → p1)) ∨ (((((True ∨ False) → (p5 → (p2 ∧ True))) ∧ p4) ∧ ((True ∧ p3) ∨ (p1 ∧ False))) → False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65696203991610787624039250065 : ((p4 ∨ ((True → (p3 → (p5 ∨ ((p3 ∧ ((p4 ∨ False) → (False → p5))) ∨ ((True ∨ ((True ∨ True) ∧ False)) ∨ (p1 → p1)))))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71514470697254446664708942179 : ((((p1 ∨ p3) → ((p4 → (((((p2 → (True → False)) ∧ p2) → ((p2 ∧ p3) → (p4 → p3))) ∧ (p5 → p4)) ∨ p4)) ∧ False)) ∧ p1) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p1 ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212319239853087309093365783597 : ((p1 ∨ (True ∨ (True → True))) ∧ (((p3 ∨ p5) ∧ (p4 ∧ ((p2 → ((((True → False) ∨ p1) → (False → p3)) ∨ (p3 ∧ p2))) → p2))) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134456824394357746207858678445 : (((((p1 ∨ ((False ∨ (p3 ∧ p3)) ∨ (p5 ∧ (p1 ∧ p2)))) → ((((p4 → p5) → False) → True) → p1)) ∧ p1) → p4) ∨ (False → (p4 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51388454154709697298035980189 : (((((False ∧ p2) → (True → ((p4 ∧ True) → (((p4 → p4) → (True ∨ p3)) → p3)))) ∨ p1) → (True → ((p4 ∨ False) → (p2 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718649604918079360111176405346 : (((((p1 ∨ p1) ∧ (p5 → True)) ∨ (((True → (p4 ∧ False)) ∧ ((p3 ∨ True) → (((p4 ∨ p1) → ((p3 ∨ p4) ∨ p2)) → p4))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20902364354164542199622089887 : ((((p5 ∨ p5) → (((False ∧ ((p2 ∨ False) ∧ p4)) ∨ p5) ∧ p5)) ∨ (False ∧ ((True ∧ False) ∨ (True → (((p2 ∧ p4) ∧ False) ∨ p4))))) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157963992048466736446519867318 : (((((p5 ∨ p3) ∨ p2) ∧ ((p1 ∨ p1) ∨ p3)) ∨ (((False → (p3 → p1)) → (False → False)) ∨ True)) ∨ (p3 → ((p1 ∧ (p4 ∧ False)) ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43268904125597426424605041774 : ((((p4 → (p5 ∨ (((p1 ∧ ((True ∨ (((p2 ∨ p5) → ((p5 ∧ True) ∨ p3)) → True)) → (False → p2))) ∧ False) → False))) ∧ p3) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263384917779384005984898403552 : (True ∧ (((True ∨ (p1 → (((p5 ∨ (p2 ∨ p1)) ∨ p1) → (((p1 → p2) ∧ p2) → (p5 ∨ (p4 → p2)))))) → p5) ∨ ((p1 ∧ False) → p2))) := by
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
theorem thm_5_vars_348284750936437244058347132187 : (p3 → (True ∧ (False ∨ ((True ∧ ((True ∧ ((True ∨ (((p5 ∧ p2) → p4) ∧ False)) → (p4 ∧ (p4 ∨ (p1 ∧ p3))))) → p1)) ∨ (True → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605986012717077998273072098959 : ((((p5 → ((((p4 ∨ p2) ∨ (p5 ∧ False)) ∨ (p2 ∧ p1)) → (((p5 ∧ p4) ∧ False) ∧ ((p1 → (p2 → (p5 ∨ p5))) → False)))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4057421330555325440026720297 : (p2 ∨ ((False ∧ p5) ∨ ((p4 ∧ ((False ∧ p4) ∨ p1)) ∨ ((False → p3) → (True ∨ (p1 → ((p2 ∧ p1) → ((p4 ∧ p5) → False)))))))) := by
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
theorem thm_5_vars_187074560248133841565225181955 : (((p5 ∨ True) ∧ (p1 ∨ (((p2 → (p1 ∨ p2)) ∨ p5) ∧ True))) → (((False ∨ p3) ∨ (False ∨ (((p4 ∧ True) ∨ (p3 → True)) ∨ p4))) ∨ p2)) := by
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
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
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
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
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
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h15 =>
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
      intro h16
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h20 =>
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
        intro h21
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h22 =>
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
        intro h23
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42347497230473540938339270781 : (((p3 ∧ ((p5 → ((p4 ∧ p2) ∨ ((p3 ∧ (p5 ∨ (False ∧ True))) → p4))) → (((False ∨ p1) ∨ (False ∧ p5)) ∨ (p5 → p4)))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623379726164637080508640296407 : ((((False ∨ ((((False → p1) → p2) → ((p1 ∧ False) ∨ (True → ((p4 ∨ ((p5 ∨ p1) → (p2 ∧ (p3 ∨ p1)))) → p1)))) ∧ True)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_59250687606254104359985566252 : (((p2 ∨ p4) ∨ (((p4 → p5) ∨ (((((p2 ∨ (False → p1)) → (p1 → p2)) ∧ p4) ∧ (True → p1)) ∨ True)) ∨ ((p1 ∨ True) → p1))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111954242092484091418605679615 : (((((p4 ∨ ((p5 → p2) → (p4 ∧ p5))) → False) ∨ ((((False ∧ True) ∨ (False ∨ p1)) ∧ (False ∨ False)) ∨ (p5 ∨ p1))) ∨ p4) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87439088417341942849449632192 : (((True → ((False ∧ p5) ∧ (p1 ∧ p2))) ∧ (((False ∨ (p5 → (p2 → (((p2 ∧ p2) ∧ True) ∨ ((p1 ∧ p3) ∨ p4))))) ∧ False) → p2)) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231961248985871481424126849673 : (((p1 ∨ p3) → False) → ((((((p1 ∨ (p1 → (p1 → (False ∧ p4)))) ∧ (False ∨ p4)) ∨ (p2 ∨ True)) ∨ p3) ∨ (p5 ∨ p3)) ∨ (p1 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_113549153449823072297877255960 : ((((False ∧ (p1 ∨ False)) ∨ ((((p3 ∨ (p1 ∧ True)) → (((True ∨ p4) ∧ True) → (p2 ∨ True))) ∨ p2) ∨ True)) ∨ (p4 → p2)) ∨ (False ∨ p5)) := by
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
theorem thm_5_vars_151890647304609285819262926340 : (((((p2 → ((True ∧ p3) ∧ ((p5 → False) ∧ False))) → p1) → (p4 ∨ True)) → ((p3 ∨ p5) → (p3 → p5))) → ((p3 ∨ (False → True)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60565051848408830349985945244 : ((True ∧ (((True ∧ ((p3 ∧ (True ∧ p5)) ∨ (((p4 ∨ (((p3 ∨ True) ∨ p5) ∨ True)) → ((p2 ∨ p4) → p2)) → True))) ∨ p4) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179361225925408238896215520185 : ((p2 ∨ ((p4 ∧ ((p1 → ((True → p4) ∨ p5)) ∧ p4)) ∨ (p1 ∧ p4))) ∨ ((((p5 ∧ False) ∧ p1) ∨ True) ∧ (False → (p5 → (p3 ∧ p3))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112897532673734860987469416372 : ((((p3 → True) ∧ ((p2 ∧ (p4 → (((p1 ∧ p4) ∧ (p3 → p2)) ∨ ((p5 ∨ p2) ∧ p5)))) ∨ (p5 ∧ (p3 → p1)))) → False) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113876689810890658327780180737 : ((((((p4 ∨ (p3 → p4)) ∨ p2) ∧ (((p5 ∧ True) ∧ (p5 → ((p1 ∧ p1) ∧ p4))) ∨ p1)) ∧ p2) ∧ ((p1 ∨ p2) ∧ p4)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



