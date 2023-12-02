variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199851592177777506781965505026 : (((p5 ∧ ((p5 → p2) ∧ True)) ∧ (p2 ∧ p4)) → (((p2 ∨ True) → p3) ∨ (True ∧ ((p3 → (((p5 → p3) ∨ p4) ∨ (True → p5))) ∧ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h10
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257515137900465034029352451032 : ((p3 ∨ False) → (((p2 → p5) → (p4 ∨ (p2 ∨ p1))) ∨ (((((p1 → p3) → False) → ((False ∨ p2) ∧ (p2 → (p3 ∧ True)))) ∨ False) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149112042806371404407334829595 : (((True ∧ False) ∧ ((p3 ∨ ((p4 ∧ (False → ((p1 ∨ True) ∧ p3))) → True)) → (p2 ∨ ((p1 → True) ∧ p5)))) ∨ ((False ∧ (p4 ∧ p5)) → p4)) := by
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
theorem thm_5_vars_608167655834360256768030655590 : (((((((p3 → p2) ∨ ((p2 → (p2 ∧ ((True ∧ True) ∧ (((p2 → p3) → False) ∨ (p1 ∧ (p2 → True)))))) ∨ p2)) ∧ p5) ∨ p2) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723453183587813202279352116149 : (((((p4 ∧ True) → True) ∧ (p5 ∨ (p5 ∨ (((((False ∨ p4) ∧ (True ∧ (p1 → False))) ∧ p3) ∧ p1) ∧ (p3 ∨ ((p3 ∧ p2) ∨ p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126432860797558226384046471903 : ((p2 ∧ ((True ∧ (p5 ∧ (((True → (p3 ∧ False)) ∨ p5) → ((((((True ∨ p5) → p4) ∨ p3) → p4) ∧ p2) ∧ p3)))) ∧ p3)) → (p4 ∨ p4)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : ((True → (p3 ∧ False)) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h14 : (((True ∨ p5) → p4) ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h15 := h13 h14
  -- One of the premise coincides with the conclusion.
  exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671325752313710277711143144243 : ((((True → ((((True → p5) → ((p2 ∧ (p3 ∨ (p1 → p2))) → (True → p1))) ∧ p4) ∧ (p3 → (False → False)))) ∨ (True ∨ (p4 ∧ True))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_161130321886633869162228920681 : (((False → p3) ∧ (p3 ∨ (p1 ∨ (p1 ∧ ((((False ∧ p3) ∨ ((True ∧ False) ∨ False)) ∨ p5) → True))))) → (p3 ∨ (p4 → ((p4 ∧ p5) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106565738251219024389758046620 : ((((((False ∧ True) ∨ p3) → (p4 ∨ False)) ∨ p5) → (((False ∨ True) → ((p5 → (p4 ∨ True)) ∧ ((False ∨ p2) ∧ p2))) ∨ True)) ∧ (True ∨ p5)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739331077454699227816701922630 : ((((p4 ∧ p4) ∨ ((((True ∧ (p5 → ((p3 ∧ p2) ∧ p3))) ∧ p2) → ((True ∧ (p5 ∨ ((p2 ∨ False) ∨ p2))) → (p3 ∨ p2))) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_63142615031742185788403544507 : ((p5 ∧ ((p1 ∨ (((((p5 ∨ p2) ∨ (p3 ∧ (p2 → p3))) → (((p1 ∧ True) ∨ False) → p5)) ∨ True) ∧ ((p1 → p4) → True))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313974278607468548537118505785 : (p3 ∨ (((p4 → (((p3 ∧ (True → True)) ∨ ((p1 ∨ False) → p1)) ∧ p4)) ∧ (((True ∨ p4) ∨ ((p5 ∨ p3) ∨ False)) → p3)) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680527112344241414996102941967 : ((((((p4 ∧ ((p4 ∧ (False ∧ False)) → (False ∧ True))) → p1) → (((p4 ∨ p5) ∧ p4) ∨ (p2 ∧ p3))) → (p5 ∨ ((p1 ∨ p3) ∨ True))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138219207752953282708329446029 : ((p2 → (((p3 ∨ (p5 ∧ (p2 ∧ (True ∨ ((p4 ∧ ((p3 → False) ∨ p4)) ∧ ((False ∨ True) ∨ p3)))))) → p5) → p5)) ∨ ((p5 ∧ p2) → p5)) := by
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
theorem thm_5_vars_345695420940273993895844336098 : (p3 → ((p5 ∨ ((False → False) ∧ ((p1 ∧ p3) ∨ ((p5 ∨ p2) ∨ (p5 → (((p5 → (p4 ∨ p5)) ∧ True) ∨ ((p3 → p2) → True))))))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703781678665926814075118763361 : (((((False → ((p2 ∧ ((p4 ∨ False) ∧ False)) ∨ False)) ∧ p3) → (((((p5 → p3) ∨ ((p4 ∨ p3) → (p3 ∧ False))) → p5) ∨ True) ∨ p5)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318551340408491567332006938355 : (p4 ∨ (((p4 ∨ ((p2 ∧ (((p4 → ((p1 ∧ p2) → (p1 ∧ p4))) → (p5 → (p1 → p3))) ∧ p1)) ∨ (p1 ∧ True))) ∧ p2) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264151190085246705484994168391 : (True ∧ (((((p4 → p4) ∨ p4) → (p2 ∨ p3)) ∧ p5) ∨ (p5 → (((((p4 ∧ p2) → p5) → True) ∨ (p4 → p5)) → (p5 ∨ (p3 ∧ False)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171617543857451743484269302907 : ((((p5 → ((False ∧ p5) ∧ False)) → (p2 ∨ ((False ∧ (p3 ∨ p4)) ∨ False))) ∨ p2) ∨ (((False ∨ True) ∧ p3) → (True ∧ ((p5 → p3) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47990207004081836223896562557 : ((((((p2 ∧ (True ∧ ((p5 ∨ p2) → p3))) ∨ (p5 ∧ True)) ∨ (p3 ∨ p4)) ∧ ((((p1 ∨ p1) → p4) → p2) ∨ False)) → (p2 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351020656015025039311060197076 : (p4 → ((p5 → (p2 ∧ (p4 ∧ (p3 ∧ ((((((True ∨ (p1 ∧ True)) → p2) ∧ (False → p4)) → False) ∧ p5) ∨ (p1 ∨ False)))))) ∨ (True ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158225739672202214314068122431 : (((p1 ∨ (p5 → p2)) ∧ (p1 → (p3 ∨ ((((p5 ∨ (p5 ∧ False)) ∨ (p1 ∧ p5)) ∧ True) ∧ p2)))) ∨ (p2 → (False → ((True ∨ True) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136241127111913224687784661400 : ((((p3 → p1) → ((p5 ∧ p4) ∧ False)) ∨ ((p3 ∧ ((p4 ∧ (((False → p1) ∧ p2) → (p4 ∧ p5))) → p3)) ∧ p5)) ∨ (True ∨ (True → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358474552768917590155774664339 : (p5 → (p1 → (((((p4 ∧ (p4 ∧ p2)) ∨ (((p5 ∧ (p1 ∧ True)) → p2) ∨ ((p3 ∨ p1) ∧ p1))) ∨ True) ∨ p5) ∨ ((True ∧ p4) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783225528818525465432613843045 : (((p3 ∨ (((((False → p2) → p5) ∨ (p5 ∧ p2)) → ((True ∨ (p2 ∨ p1)) ∧ (p2 ∧ (p1 → (p1 ∨ False))))) → ((True → p2) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763933539814974068039207197952 : (((p3 ∧ (True → ((p3 ∨ (p2 ∨ ((((((p4 ∨ False) → p5) ∧ ((p3 ∨ (p4 ∧ p4)) ∧ True)) ∨ (p1 ∧ True)) ∧ True) → p3))) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58937143917012851335583001362 : (((p1 ∧ p4) ∨ ((p2 → (p5 → p3)) ∨ ((p2 ∧ (True → p4)) → ((((p5 ∨ (p2 → False)) ∨ p1) ∨ (False → True)) ∧ (p4 ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115164764547760819704760974498 : ((((True ∨ (p3 ∨ (((p5 → p5) → False) ∨ p1))) ∧ p2) ∧ (((((p5 → p4) → p2) ∨ p5) → p2) ∧ ((p2 ∨ True) → p3))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246694671238077373785566696350 : ((p5 ∧ p4) ∨ ((p4 ∨ (True → ((((True → ((p5 ∧ (p5 ∧ p5)) ∨ True)) → (p4 → p5)) ∨ (True ∨ p2)) ∨ p3))) ∨ ((False ∧ True) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_684642218365429075128244473970 : ((((((p3 → p4) ∧ p5) ∨ ((((p4 ∧ p2) ∧ p3) → p3) → (p1 ∧ (False ∨ (True → p5))))) ∨ ((p3 ∨ (p5 → True)) → (True ∨ p2))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152768781090142981582991309500 : (((p5 → p4) ∨ ((((p3 → p3) → p2) → p5) ∧ (p1 ∨ (p2 → (((p3 ∨ p3) → False) ∧ (p2 ∨ p4)))))) → (p3 ∨ (p1 ∨ (False → p5)))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57739014202356128562682853833 : ((((p4 ∨ p5) → p1) → (((((p1 ∨ True) → (((p1 ∨ p5) → p4) ∧ p4)) → p5) → p3) ∧ (p5 ∨ ((False ∧ p2) → (p4 → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761454796918114494015970512601 : (((p3 ∧ ((False ∨ ((False ∧ ((p4 ∧ (p2 ∨ (False ∨ (True → (p3 → p1))))) → (True → ((p1 ∨ p2) ∧ (True → p4))))) ∨ True)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55587088598931588350855690641 : (((p3 ∨ (((p4 ∧ p3) ∧ p2) → p5)) → (((p4 ∧ p5) → p2) ∧ (((p4 ∧ (p3 ∨ (p5 ∧ (p1 ∧ p4)))) → False) → (p2 → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187165223112713857118763363181 : (((p5 → p3) ∨ ((((p5 ∨ p5) → (p1 ∧ True)) ∨ p5) → p2)) → ((p2 ∨ ((p3 ∨ True) ∧ p3)) ∨ (False → (((p5 ∨ True) ∧ True) ∨ p4)))) := by
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
theorem thm_5_vars_307140839054514783846871475273 : (p1 ∨ (False ∨ ((((p3 ∨ ((((p1 ∧ p3) ∨ (True ∧ False)) ∨ p5) → p5)) ∨ p3) ∨ True) ∨ (((True ∧ p2) → True) ∧ (p4 → (p2 ∧ False)))))) := by
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
theorem thm_5_vars_208578396179005585404714921281 : (((False → False) → ((p5 ∨ p2) ∧ p1)) → ((((False → p5) → ((p4 → (p3 ∧ (p2 → p5))) → (True → (p2 → (p4 ∨ False))))) ∨ p1) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → False) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318561003886546811806005187726 : (p4 ∨ (((p2 ∧ ((p4 ∨ (((True ∧ p3) → ((p4 → p3) ∧ (p1 ∧ ((True ∧ p4) ∧ p3)))) → (p5 ∨ p3))) ∨ p1)) ∨ True) ∨ (p3 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245335101179327768859103868148 : ((p2 ∧ p2) ∨ (p5 → ((p2 ∧ p3) → (False ∨ ((((False ∨ p4) ∧ True) ∨ ((((True ∧ False) ∨ p4) ∨ p2) → p5)) ∨ ((False → p3) ∧ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675286305665012561999038762279 : (((((p4 → (((p4 ∧ (p4 ∨ True)) ∧ (p3 → (((p4 → p4) ∨ False) → p5))) → (True → p2))) ∨ True) ∧ (p4 ∨ (False → (p3 → p5)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804360173993017241498997528311 : (((p3 → (((p1 → (((p5 → (False ∨ p3)) ∨ True) → (p3 → p4))) → True) → (((p1 ∨ p2) ∧ ((True ∨ (p5 → p3)) → p2)) ∨ True))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49745454631342267170155260555 : (((p4 ∧ ((p5 ∧ (True → (p2 ∨ p1))) ∧ (((p2 ∧ ((((p3 → p5) ∧ p3) → False) ∧ False)) → p4) ∧ p5))) → ((p4 ∧ p1) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323893943440868223373963650463 : (p5 ∨ (((((p1 ∨ p2) ∧ ((p4 ∨ p3) → p4)) → (p3 → (p5 ∧ p2))) ∧ (True ∨ p1)) ∨ (p5 → ((p3 ∧ (p3 ∨ (True ∧ p2))) → True)))) := by
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
theorem thm_5_vars_44719757617240756070073708662 : ((((p2 → ((False ∧ True) ∨ p3)) ∧ ((False → (((True ∧ ((p1 ∨ (p3 ∧ p3)) ∧ False)) → (p4 ∨ (p5 ∨ p4))) ∧ p2)) ∨ True)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163991936435086527127591984683 : ((True ∨ ((False ∨ (((p2 → True) ∧ (True ∧ p1)) ∨ ((p2 ∨ p4) ∧ (False → p1)))) ∨ p2)) ∧ ((p3 ∧ (p2 ∧ p3)) ∨ (p4 ∨ (p3 ∨ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204706001302691393786951174520 : (((p5 ∨ ((p2 ∧ p4) ∧ p1)) ∨ False) ∨ (((p3 → ((False → p1) ∧ p3)) ∨ ((False → p5) ∨ (p3 → (((p5 ∧ True) ∧ p1) ∧ p1)))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324260341896048408936580302472 : (p5 ∨ (((((p2 ∧ p1) → p3) → p4) ∧ (p3 ∧ p2)) ∨ (((p4 → ((p5 ∧ p4) ∨ (p4 ∨ ((False ∨ p5) → p4)))) ∨ (p4 ∨ p5)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184567716951727280144931030573 : ((((p3 ∨ (p3 ∨ p5)) → (True ∨ (False ∨ p1))) → (p2 → False)) ∨ ((p1 ∨ (p1 ∨ p1)) ∨ (((p2 ∨ False) → (p3 → True)) ∨ (p3 ∨ p2)))) := by
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
theorem thm_5_vars_886517146635075934066955213235 : ((((((p2 → (p1 → (((False ∧ (p3 ∧ False)) ∧ (p3 ∨ p2)) ∨ (p4 → (((False ∧ False) ∨ p4) → p2))))) ∨ p4) ∨ False) → (False ∧ p2)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 → (p1 → (((False ∧ (p3 ∧ False)) ∧ (p3 ∨ p2)) ∨ (p4 → (((False ∧ False) ∨ p4) → p2))))) ∨ p4) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h2
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- False on the left can always be used.
  apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689600864745429159164742860529 : ((((((p1 ∨ (p3 ∨ p4)) ∧ (p5 ∨ p3)) ∨ ((False ∨ p5) → ((p4 ∨ p4) → p5))) ∨ ((False ∨ ((p5 → False) ∨ p5)) → (p3 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302654887057472744785571720899 : (False ∨ (p2 ∨ ((p5 → p5) → (p1 → (False ∨ (p2 ∨ ((p3 → (((((p5 ∧ True) ∨ p1) → (p1 ∧ False)) ∨ p3) → (p4 ∨ p1))) ∨ p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167998940897617116339302169765 : (((p3 → ((p1 → p4) ∧ (p3 ∨ p3))) ∧ (True ∨ (((p1 ∨ p4) → p3) → (p4 → p2)))) → (p3 → (((False → True) → p1) ∨ (p3 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57011462539486650119177863799 : (((False → (p5 ∧ True)) ∧ (((p3 ∧ ((p3 → p4) ∨ p5)) → (p1 ∧ p5)) ∨ (((((True ∧ False) ∧ p3) ∨ (p3 ∧ False)) ∧ p3) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338636244927189004246641477523 : (p1 → ((True ∧ p1) ∧ (p4 → ((((((p1 ∨ p4) ∨ p5) → False) → (p3 ∧ ((False → p2) ∨ p2))) → p5) ∨ (((True → p4) ∨ p5) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134156736898901286616642545730 : (((((p4 ∧ (((p1 ∨ p3) ∧ ((p5 ∨ p5) → (False → p5))) ∧ (False ∨ p4))) ∨ p2) → ((p3 ∧ p2) ∧ False)) ∨ True) ∨ ((p1 ∧ p5) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166188027641709836080922336012 : ((p1 ∧ ((p3 → (p2 → ((((p5 ∧ (False → (p1 → p3))) ∨ p3) → p2) ∧ True))) → p3)) ∨ (False → (((p3 → p2) ∨ (p4 ∨ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157100711033890006928031771699 : (((p2 → (((((p2 ∨ (True → p1)) → ((True → (False ∧ p4)) ∧ False)) ∨ False) ∨ p2) ∨ True)) ∨ p5) ∨ ((p4 ∨ ((True → p4) → p4)) ∧ p1)) := by
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
theorem thm_5_vars_680616740409300504918362812831 : (((((((False → (p4 ∨ p4)) → False) ∨ p3) ∧ (((False ∨ (p4 → (p5 ∨ False))) ∨ True) ∧ (True → p1))) → ((p5 ∨ (p4 ∧ p1)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803472903594435576100968467875 : (((p3 → (((((p3 ∨ p4) → ((((p4 → p3) ∧ (True ∧ (True ∧ p2))) ∨ ((p5 ∨ p2) → p2)) → p1)) → (p1 → True)) ∨ p5) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319869058464912572493725030946 : (p4 ∨ (((p2 ∧ p3) ∧ (p1 ∧ p3)) ∨ (True ∧ ((True ∨ ((True ∨ p3) → p4)) ∨ (((True ∨ True) ∨ ((p5 ∨ (True ∧ p2)) ∧ p4)) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330720258696139007614070989289 : (True → (p1 → (((p5 ∧ ((True ∧ (p2 ∧ ((p4 ∧ (p1 ∨ p2)) ∨ ((p5 → p1) ∧ p2)))) ∧ (p3 ∧ ((p5 → p5) ∧ False)))) ∨ p1) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338587553045950885713448353503 : (p1 → (((p1 → p4) ∨ p2) → (((p4 → p3) → ((p4 ∧ (p5 ∧ (p1 ∧ (False → ((True ∨ p5) ∧ True))))) ∧ (p5 → p1))) ∨ (p5 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249494624939332783674489358803 : ((p5 ∨ p1) ∨ (((True ∧ ((((p1 ∧ p1) ∧ p2) ∨ p3) ∨ p1)) ∨ (p3 → True)) ∨ (True → ((p3 ∨ (p5 ∨ ((p2 → p4) ∧ p5))) ∧ p3)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113248841852913126597066211389 : ((((((False → (p4 ∨ p3)) ∨ (False ∨ (p2 ∧ (p5 → (p4 → ((p5 ∧ p5) ∧ True)))))) → p1) ∨ (p3 ∨ p2)) ∧ (p3 ∧ p3)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738623610254085513184838987215 : ((((p2 ∧ False) ∨ ((p5 ∧ ((p3 → (((False → p1) ∨ False) ∨ ((False → (False ∨ ((True ∨ p4) ∨ p5))) → p1))) → (p3 ∨ p5))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621268769751007919280304283306 : ((((True ∧ ((((p3 → p4) ∨ (p1 ∨ (p5 → p1))) → (((p3 → ((p2 → True) ∧ p5)) → p3) ∨ False)) → ((p3 ∧ p3) ∨ p1))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_173210073021642781073298529160 : ((p5 ∨ (((p5 ∨ (p3 ∨ p4)) ∧ p4) ∨ (((p3 ∧ p2) ∨ (p5 ∧ p3)) → p5))) ∨ ((False → p2) ∨ ((p3 → ((p4 ∧ p1) ∨ p4)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115507886935473544234479559946 : ((((((p5 ∨ p2) ∨ False) → p1) ∨ (p3 ∧ p1)) → (((((p1 ∨ True) ∨ p4) → False) ∧ (False ∨ (False → True))) ∨ (p2 ∧ p5))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197951231642568621414619175563 : (((p2 ∧ p4) ∧ ((p1 → p4) ∧ (p1 ∧ p1))) ∨ (p1 ∨ (False ∨ (p2 ∨ (((p4 ∨ p3) ∨ (((p2 ∨ p1) → True) ∨ (p4 → p2))) ∨ p4))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66812797213573924668801267657 : ((True → (p5 ∨ (((((p4 → p3) → (True ∧ p5)) ∨ ((True ∧ (True ∧ p4)) ∧ (False ∧ (((p4 → p5) ∧ True) ∨ True)))) → p3) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603321651159861355194320285753 : ((((p2 ∨ (p2 ∨ (((True → p2) ∧ p2) ∧ ((True ∧ False) ∨ (((p5 ∧ (p2 ∨ p2)) → p5) → ((p2 ∧ (p3 → p4)) ∧ p4)))))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629298749942303962202824239909 : (((((((True ∨ (((p3 ∧ p2) → (((((p3 → p3) → (p2 ∨ p4)) ∧ False) ∨ True) ∧ p3)) → p1)) → (p3 → p4)) → p3) ∨ p4) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_993051647860626423785884035273 : (((p4 ∧ (p3 ∧ (((False ∧ ((p2 ∨ p2) ∨ (True → (((False → p5) ∨ p5) ∧ p1)))) ∨ (p5 → ((p4 ∨ True) ∨ p3))) → (p3 ∧ False)))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((False ∧ ((p2 ∨ p2) ∨ (True → (((False → p5) ∨ p5) ∧ p1)))) ∨ (p5 → ((p4 ∨ True) ∨ p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42661433561709901831052462414 : (((p4 ∨ ((p4 → (False → (p1 ∨ (p2 → ((p1 ∧ p1) → ((p4 → p2) ∧ p2)))))) → (False ∨ ((p4 ∨ (p2 ∨ False)) ∧ p4)))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172559974823030682826605304015 : (((p1 ∧ (p3 → p5)) ∨ (p3 → (((p1 → False) ∧ (p4 → p1)) → (p4 ∨ p5)))) ∨ ((((False ∨ (False ∧ (True ∨ p5))) ∨ p1) → True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40477194541511499209358057003 : (((((p1 ∨ p4) ∧ (p3 ∨ ((p3 ∨ ((((p1 ∧ p4) ∧ p1) ∨ ((p4 ∨ (False → p3)) ∧ p3)) ∧ (p5 → p1))) → False))) ∨ True) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49508085510086507148167131592 : ((((p3 → ((((False ∧ (p1 ∧ (p3 → p3))) ∨ p2) ∧ p5) ∧ (p2 ∨ ((p3 → False) ∨ (p3 → p5))))) → True) → ((p4 ∨ p2) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61813152490106474131287218046 : ((p2 ∧ ((((True ∨ p5) → ((p1 ∧ p2) ∧ (p2 ∨ (p5 ∨ (True ∧ p4))))) ∧ (p3 ∨ (((p2 ∨ True) ∧ p4) ∧ (p2 ∨ p2)))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261390991311722566091069013364 : ((p5 → p1) → (((p5 ∧ (p2 → False)) ∧ (p5 ∧ (p1 → ((True ∨ (True ∧ ((p3 → (True ∧ p3)) ∨ p1))) ∧ p4)))) ∨ ((p5 ∨ p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37642393976993853536116228391 : (((((p2 ∧ (((p4 ∨ False) ∨ True) ∧ (True ∧ ((((p2 ∧ False) → False) → p4) ∧ ((p2 ∨ (True ∨ p4)) ∨ p3))))) ∨ p3) → p4) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46611298409197713865933194768 : (((p2 ∧ (p5 ∨ ((p4 ∨ ((p2 ∧ ((True ∧ ((True ∧ p1) ∧ False)) → False)) ∧ True)) ∧ (((True ∨ p2) → p3) ∧ True)))) ∧ (p2 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118307464194418029239518664922 : ((p1 ∨ (p2 ∨ (((p1 ∨ True) → ((p4 ∧ p1) ∨ (True ∧ (p1 ∧ (p3 → (p5 → (p1 ∧ p1))))))) ∨ ((False → p5) → True)))) ∨ (p4 → p3)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721425013137456201213149934291 : ((((p1 ∧ ((p5 ∧ p1) ∨ p5)) → ((p3 ∧ p4) ∨ ((((p4 ∨ p4) → (True → ((p2 ∨ False) ∧ False))) → p2) ∨ (p3 ∨ (p1 ∨ True))))) ∨ p1) ∧ True) := by
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
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57738223560544111125446407600 : ((((p4 ∨ p3) → p4) → (p5 ∨ ((p4 ∧ p2) ∨ (p1 ∨ ((p3 ∨ (p1 ∨ p4)) ∨ ((((p4 ∧ p1) → p5) → p3) ∧ (p5 → False))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184777546943238731850319822009 : (((((p1 ∨ False) ∧ p2) ∨ p2) ∨ (((False ∨ p1) ∧ True) ∨ p4)) ∨ (p5 → (((p1 → p5) → (p4 ∨ p2)) ∨ ((p3 ∧ True) → (True ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247794124977312276928965493016 : ((p1 ∨ p1) ∨ (((p3 → (p5 ∧ ((((True → p5) ∨ p2) ∧ p5) ∨ p4))) ∨ False) ∨ (True ∨ ((((p1 → p1) ∧ (p4 → p1)) ∨ p3) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769985779955459717003537235969 : (((p5 ∧ (p1 → (False ∧ ((p2 ∧ ((((p4 ∨ ((p1 ∨ ((p4 ∨ False) → False)) ∨ p4)) → p2) ∨ ((False ∧ p5) ∧ True)) ∧ p1)) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114673393038470550546222996733 : (((False ∧ (((p4 ∧ p3) ∧ (p2 ∨ ((p1 ∧ (p5 ∧ p2)) ∧ p4))) ∨ (True ∧ False))) ∨ ((p1 ∧ p2) → ((True ∧ True) ∧ True))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42092950516219589423389339975 : ((((p5 → p4) ∨ ((p2 → (False ∧ p2)) ∧ (((False → (p2 ∨ (p2 → False))) → (((p3 ∨ False) → p4) ∧ False)) ∧ (p5 ∧ p2)))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225979102808452832925581669942 : (((p3 ∧ p3) ∨ p1) ∨ (((((p1 ∨ ((p5 ∧ ((p4 ∨ p1) ∨ False)) → (p3 ∧ (p2 → False)))) ∨ p3) ∨ True) ∨ False) ∨ (p5 ∨ (p4 ∧ p4)))) := by
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
theorem thm_5_vars_190602094563486296572015074645 : ((((p4 → p5) ∨ (p5 ∨ (p4 → (p5 → p4)))) → p3) ∨ (p5 ∨ ((p4 ∧ p5) → (p4 ∧ (p2 → ((p4 → ((p4 → False) → p3)) ∧ p4)))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h9 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h10 := h6 h9
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164581962067245149722086320222 : ((((p2 ∧ p1) ∧ ((p4 ∧ ((p1 ∨ False) ∨ (False ∧ p2))) ∧ (False → (False → p3)))) ∧ p4) ∨ ((p2 ∨ (p4 → p4)) ∨ ((p5 ∨ p4) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337672384603932924216286991072 : (p1 → (((p4 → p4) → (p2 ∧ (p3 → ((p2 ∨ p3) ∧ ((p4 ∧ ((False ∨ False) → p2)) ∧ p5))))) ∨ (p2 ∨ (True ∨ ((p4 ∨ p1) ∨ p4))))) := by
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
theorem thm_5_vars_148217307322051988724692933589 : ((((((p1 ∨ p2) → ((p1 ∨ False) ∧ ((p1 → (True ∨ p3)) ∧ True))) ∨ p4) ∧ p3) ∨ ((p4 ∨ p3) ∨ True)) ∨ ((True ∨ (p5 ∨ True)) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47134795396544915584645189594 : (((((p4 ∨ ((True ∧ p4) ∨ ((True ∧ (True ∨ (True → p3))) ∧ (True ∨ p3)))) ∧ p5) ∧ (((True → p5) ∨ p4) ∧ p2)) ∨ (True ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322401365445345315592934028201 : (p5 ∨ ((((p4 ∨ (p2 → (p2 → p1))) ∧ (p2 ∧ (p5 → (p5 ∧ p1)))) ∧ ((p3 ∨ (((True ∨ (p2 ∨ p2)) → False) → False)) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616062705938271546491830580791 : (((((p1 ∨ (((True ∨ True) ∧ (p1 ∨ ((False → (p2 ∨ p5)) → True))) ∧ p1)) → (((((p5 → p1) ∨ p2) → False) ∧ p5) ∨ p4)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_116359006780024445992773511266 : ((((p3 → p1) ∨ p2) → (((p5 → (p2 ∨ True)) → ((p4 → (p5 ∨ (((False ∧ False) ∧ (False ∨ p5)) → False))) ∨ p1)) ∧ p3)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53952792013656877939002447980 : (((p5 → (True ∧ (p3 → (p1 → ((p3 → p4) ∨ False))))) ∨ ((((p4 ∧ (((p4 ∨ p2) → p2) ∧ (True ∧ p2))) ∧ p3) ∨ p5) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317822902059537069238863408748 : (p4 ∨ (((p5 ∧ (p2 ∧ (p3 ∨ p4))) ∨ (((p3 ∧ True) ∧ (p3 → p1)) → (((p2 ∧ (p4 ∧ (p1 ∧ (True ∨ p3)))) ∨ p5) ∨ p1))) ∨ p4)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- One of the premise coincides with the conclusion.
  exact h7



