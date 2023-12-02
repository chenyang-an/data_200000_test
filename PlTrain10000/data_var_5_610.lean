variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49585338829022911706572126500 : (((((True ∨ (p2 ∨ ((False → ((False ∨ False) ∧ p4)) ∧ p3))) ∨ False) ∧ (p4 ∧ ((p3 ∨ p2) ∧ (False ∨ True)))) → ((False → p2) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356165802911964716830154990853 : (p5 → ((p1 ∧ ((p3 ∧ (((((False ∧ p2) → (p2 ∧ p3)) → p5) ∧ (p4 ∨ p2)) → p5)) → p4)) ∨ ((p3 → p5) ∨ ((True ∧ True) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183919665877764123818594137922 : (((p1 ∧ (p1 ∧ (((True ∨ (p3 ∧ p1)) → True) → p1))) ∧ p1) ∨ (((p5 ∧ (p1 ∨ (p4 → (False → ((p1 → p5) → True))))) → True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59088927816980151377647402802 : (((p5 ∧ p3) ∨ (((False → True) → False) ∨ ((p4 → ((((p4 ∨ (p5 ∨ (p2 ∨ (p5 → p2)))) ∨ (p1 ∧ False)) ∨ p4) ∨ p3)) ∧ True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193674668214372300051144951429 : ((p1 ∧ (((False ∨ (p5 ∧ (p4 → p4))) → p4) ∧ p3)) → ((((True → (p2 ∨ (p3 → (False ∧ ((p1 ∨ False) → p1))))) ∨ True) ∨ True) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620791709093248668670328785564 : (((((p5 ∧ p3) → (p1 → (((p4 ∧ p2) → (((p1 ∨ p1) ∧ (p1 → p3)) → p5)) → (p5 → (True → (p4 ∨ (p2 ∧ p1))))))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_357264503812163143289343577432 : (p5 → ((p2 ∧ p3) ∨ ((((p1 ∨ p3) ∧ (p1 → (p5 → False))) → (p3 ∧ (((p3 ∨ p4) → p1) → (p1 → p2)))) ∧ ((False → p5) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h2.left
  let h14 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h15 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h16 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h17 := h14 h16
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h18 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h19 := h17 h18
    -- False on the left can always be used.
    apply False.elim h19
  case inr h20 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h21 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h22 := h14 h21
    -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
    have h23 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h22, we can now drive its conclusion.
    let h24 := h22 h23
    -- False on the left can always be used.
    apply False.elim h24
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h25
  -- False on the left can always be used.
  apply False.elim h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42852365574171114215900515730 : (((p2 → (((True → (((p2 ∨ ((False ∧ True) → p2)) ∧ (False ∧ (p4 ∨ (p3 ∧ p3)))) ∨ p4)) ∧ (p1 ∨ False)) ∨ (p5 ∨ p2))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681587611118817281355112628860 : ((((p1 → ((p3 → False) ∧ ((False ∨ ((p1 ∨ ((p3 ∧ True) ∨ (True ∨ p1))) → p3)) ∧ (True → False)))) → (p3 ∧ (True ∨ (p2 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802508597029391091522113752146 : (((p2 → (p3 ∨ ((p1 ∨ (((p1 ∨ (False → True)) ∧ p4) → (((p5 ∨ p5) → (p3 ∨ p3)) ∨ (False ∧ p5)))) ∨ (True ∨ (p4 ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149228078927528000369693925786 : (((p4 ∧ p1) ∨ (((p4 ∨ ((p1 ∨ ((((p2 ∨ p2) ∨ p5) → (p1 ∧ True)) → p4)) ∨ p1)) ∧ True) ∧ p1)) ∨ ((p1 → (p1 ∧ p1)) ∨ p3)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194746887514281735323590028395 : (((p5 ∧ (((p5 ∨ p3) ∨ p4) ∧ p3)) ∨ True) ∧ (((p5 ∧ True) → ((True → True) ∨ (((p1 → p5) → p2) → (True → p4)))) ∧ (p1 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62484699543305213867593902645 : ((p3 ∧ ((False → p4) → ((False ∧ (False → (((p3 ∨ (p1 → True)) ∨ ((p3 → p1) → True)) ∧ False))) ∧ ((False ∨ (p4 ∧ p5)) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190342952584140757547208554599 : (((((False ∧ p2) ∧ p5) ∨ (p2 ∨ (p2 ∨ p1))) ∨ p5) ∨ ((((p2 ∧ (False → p4)) ∧ True) ∧ ((p2 ∧ p4) ∧ p1)) → ((p1 ∧ p1) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h6.left
  let h12 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h11.left
  let h14 := h11.right
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153376747294045001004762532874 : ((p2 ∨ (p5 → ((((((p4 ∨ p3) ∨ p4) ∧ p2) → p2) ∧ False) ∨ ((p4 → (p3 ∨ p4)) ∧ (True ∨ p3))))) → ((p4 ∧ (p5 ∨ p2)) ∨ True)) := by
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
theorem thm_5_vars_180351283217542855800868407990 : ((((((((p2 → p2) ∨ p5) → False) ∨ True) → p3) ∧ p3) ∨ (p5 ∧ p3)) → ((((p3 ∧ p1) → p1) ∧ True) ∧ ((p5 → False) ∨ (False → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252039407412300007318690550903 : ((p4 → p1) ∨ ((((((p3 ∨ (p5 → p2)) → p4) ∧ p2) → (True → p3)) → (False ∨ (p5 ∧ ((True ∧ p4) ∧ True)))) → (p2 ∨ (p1 → True)))) := by
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
theorem thm_5_vars_64801250271087316459225842853 : ((p2 ∨ ((p3 ∧ (True ∧ (p2 ∧ (p2 ∨ (p4 ∨ ((False → False) ∧ ((p1 ∧ ((p1 → p1) ∧ p1)) ∧ (p2 ∧ (p5 ∨ False))))))))) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_504177723315292144395417152208 : ((((p3 ∧ (True → p3)) → ((p1 ∨ ((((p3 → (p4 ∧ p3)) → p2) → (p5 ∨ (False ∧ (p5 ∧ p2)))) → p5)) ∨ ((True ∨ p2) ∧ p3))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174515350168117511940195254751 : (((p3 ∨ (((p4 ∨ p3) → True) → p3)) ∨ (p5 ∧ (False ∨ (p3 ∧ (p4 ∧ p1))))) → (((p5 ∨ (p4 ∧ ((p3 ∨ False) → False))) ∧ p2) ∨ p3)) := by
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
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h5 : ((p4 ∨ p3) → True) := by
        -- Implications on the right can always be decomposed.
        intro h6
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h7 := h4 h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61774351505626738730289978013 : ((p2 ∧ (((((True ∨ ((p5 ∧ p5) → p1)) → p1) ∨ ((p4 ∨ True) → False)) → ((p1 ∨ p4) ∧ (p5 ∧ (True → (p5 ∧ True))))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200707921722427486223326288826 : ((p2 ∧ (p2 ∧ (True ∧ (p1 ∧ (p4 → False))))) → ((((p4 ∨ False) ∨ True) → p5) ∨ (((True ∧ p4) ∨ ((p3 → (False ∨ p1)) → p5)) ∨ True))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709153635868461427076970388530 : (((((p5 ∨ (p3 → True)) → ((p5 → p1) → p2)) → ((((p1 ∧ (False ∨ p1)) ∧ p5) → ((p3 ∨ p2) ∧ p2)) ∨ ((p1 ∧ False) ∧ p2))) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : (p5 ∨ (p3 → True)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h9
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : (p5 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h11
    -- One of the premise coincides with the conclusion.
    exact h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h2.left
  let h15 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h18 =>
    -- False on the left can always be used.
    apply False.elim h18
  case inr h19 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h20 : (p5 ∨ (p3 → True)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h21 := h1 h20
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h22 : (p5 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h23
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h24 := h21 h22
    -- One of the premise coincides with the conclusion.
    exact h24
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178660920382420543250367212746 : ((((p4 ∨ (False ∨ p1)) → p2) ∧ (p2 ∧ ((p3 ∨ p5) ∧ (True ∧ p2)))) ∨ (((p4 ∨ (p1 ∧ p1)) ∨ (p3 ∨ (True → (False → p4)))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257862768733960003443465227963 : ((p4 ∨ True) → (((((p5 → p3) → p1) → (True ∧ ((p2 ∨ p2) ∨ ((p3 ∧ True) ∧ ((p3 ∨ (p1 → p2)) ∧ True))))) ∨ True) ∧ (p4 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61564214466772752360299850932 : ((p1 ∧ ((p1 ∨ (True ∧ (p3 → (p5 → p1)))) ∧ ((((p5 → p2) ∧ p1) ∧ True) → ((((p5 ∨ p1) ∧ (p2 → p3)) → p5) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683896421664365876498527376752 : (((((p1 → ((p4 ∧ (p5 ∨ (((p5 ∨ p1) ∨ True) ∧ (True ∧ p1)))) ∧ (p2 ∨ p2))) ∨ p5) ∨ (True ∧ (p3 → (p5 ∨ (p3 ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246728513579641122255879659702 : ((p5 ∧ p4) ∨ (p1 → ((p2 ∨ (((True ∨ p2) ∨ (True → False)) ∧ (p2 ∨ p5))) ∨ (p2 ∨ (True ∨ (p1 → (p3 → ((p3 ∨ p1) → p2)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_358580222495093084674398706534 : (p5 → (p3 → (((((((((p5 ∨ False) → (p5 → ((p5 → p3) ∧ p1))) ∧ True) ∨ p2) → p2) ∨ ((False ∨ p5) ∨ p3)) → False) → p1) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((((p5 ∨ False) → (p5 → ((p5 → p3) ∧ p1))) ∧ True) ∨ p2) → p2) ∨ ((False ∨ p5) ∨ p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246408650579728006600810466742 : ((p5 ∧ True) ∨ ((p1 ∧ p2) ∨ (False ∨ ((False ∧ (((False ∧ True) ∨ p4) → (p3 ∧ p2))) ∨ (((p4 → ((p2 ∧ p3) → p3)) ∨ p3) ∨ p1))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65405216385360128278239825508 : ((p3 ∨ ((True ∧ ((False ∧ p5) ∧ p1)) ∨ (p5 ∨ ((p5 ∧ p5) ∨ (((p4 ∨ p2) → (p4 → p4)) → ((p2 ∧ (p2 ∨ p5)) → p2)))))) ∨ p4) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134162225570690418893598430757 : ((((p1 → ((((False ∧ p4) → ((p5 ∨ p4) ∧ (p4 ∧ False))) ∧ p5) → (p1 ∨ False))) → ((p2 → p5) ∨ p1)) ∨ p4) ∨ ((p4 ∨ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67799698773732364591881352057 : ((p2 → ((((((p5 ∨ (False → False)) → (p3 → ((True ∧ True) → (p2 ∨ p4)))) ∧ (p5 ∨ p1)) ∧ p3) ∧ (p5 → (False ∨ True))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619492256436820963763022879052 : (((((True → (p3 ∨ p1)) → (p3 → ((p2 ∨ p5) ∧ (((p5 → p3) ∨ ((p3 ∧ True) ∨ (((p5 ∨ p1) ∨ p4) → p4))) → False)))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_44623024602461645891807203528 : (((((False ∧ ((p1 ∧ False) ∨ False)) → p3) ∧ (((p2 ∨ False) ∨ p4) ∨ (((p3 ∨ False) ∨ (p2 ∧ ((False → p5) ∧ p2))) ∧ True))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177657009179883404277036531891 : (((((p1 ∨ (p5 ∨ False)) ∨ (p2 ∨ (True ∨ (p1 ∧ p5)))) ∨ p5) ∧ p1) ∨ (p3 → (p2 ∨ (True ∨ ((p4 ∧ p5) ∧ (True ∧ (True → p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45451736512463358551789394996 : (((True ∨ (p1 ∧ ((p5 ∨ ((p3 ∨ (p5 ∧ p5)) → (((p1 ∨ p3) ∧ (p2 ∨ p4)) ∨ p2))) ∨ ((p4 → (p2 → False)) → p5)))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187385861886232369566250605349 : ((p4 ∧ ((False ∨ (((True → (True ∧ p3)) → p1) → False)) ∧ p2)) → (((p4 ∧ (p3 ∧ True)) ∨ (p1 ∨ p2)) ∧ ((True ∧ p1) ∨ (p4 → p4)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65520223126982865275658551674 : ((p3 ∨ (p2 ∨ (((False ∧ (p1 → (p4 ∨ ((p3 ∧ p3) → p5)))) ∨ (p5 ∧ ((((True ∨ True) → p5) → p4) ∨ (p1 → p2)))) ∨ True))) ∨ p4) := by
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
theorem thm_5_vars_136395535532372491204868458494 : (((p5 ∧ (p2 → (False ∧ False))) ∨ (p4 → (p4 → (((((p2 → False) ∧ (p4 ∨ (p5 ∨ p2))) ∨ p2) ∨ p1) ∨ p4)))) ∨ ((p3 ∧ True) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_158034051904437142374517086055 : (((p3 → (p2 → ((False ∧ p1) → p3))) ∧ ((p3 ∨ (p4 → p3)) → (p5 → (True → (p2 → p4))))) ∨ (p1 ∨ (((p4 → p4) ∨ p5) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213982643847723818344335269365 : (((p5 → (True ∧ p2)) ∨ False) ∨ (((((p5 ∧ ((p5 ∧ p1) ∧ p4)) ∨ p3) ∧ ((p3 ∧ p3) ∨ (False ∧ p3))) ∧ (True → (False ∨ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342009417699471404978967789259 : (p2 → ((p2 ∧ ((p5 → ((p5 ∧ (p2 → ((p1 ∧ (p5 → False)) ∨ p1))) ∧ ((p5 ∧ (p2 ∨ p5)) → False))) ∨ p5)) ∨ (False → (p3 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148121635732510821203830076824 : (((((p3 → (p5 ∧ p2)) ∨ p2) → ((p4 → (((False ∨ p5) ∧ p2) → p2)) ∧ (p4 → False))) → (p5 ∧ p4)) ∨ (((p1 → p1) ∨ p5) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58935666680197452430513713674 : (((p1 ∧ p4) ∨ (((p4 → (((False ∨ ((p3 → p2) ∧ p5)) ∧ (p4 → p2)) ∨ (p4 → (p1 ∨ True)))) ∨ p4) ∧ (p1 ∧ (p3 → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161968848378914175880461175532 : ((p2 → (p3 ∨ ((True ∨ (False ∨ True)) ∧ (p4 ∨ (p5 → (True ∧ ((p3 ∧ p3) ∧ (p5 → True)))))))) → ((p2 → False) ∨ ((False → p1) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60212377151153722820293173860 : (((True → False) → (((p2 ∨ (((p2 ∨ p4) ∧ (p2 → False)) ∨ (p3 → p2))) ∧ ((p2 → p5) → True)) ∧ ((p4 → (p2 ∧ p5)) → p5))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634726011729415147037076869155 : (((((((p5 ∨ (p5 ∨ (((False → ((p4 ∨ p3) → p3)) → p2) ∨ (True ∨ p2)))) → (p4 ∧ False)) → p1) ∨ ((True ∨ False) ∨ p4)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320312505229097377217497783878 : (p4 ∨ ((p1 ∨ p1) ∨ ((p5 ∧ True) ∨ (((True → (p4 ∧ (((p3 ∧ p1) ∧ ((p3 → p2) ∧ p5)) ∧ p5))) ∧ p5) → (p5 → (p1 ∧ True)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313040014489113883769966505169 : (p3 ∨ ((((((((((True → (p4 → (p5 ∧ p2))) ∨ p3) ∨ p3) ∨ False) ∨ (p5 ∧ (False → False))) ∨ False) ∧ p1) ∧ (p1 ∧ True)) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150036498594242864732611016135 : ((p5 ∨ (p5 ∧ (p5 ∧ ((p4 ∨ ((((((p4 ∨ p2) → True) ∧ (p3 → p3)) ∧ p4) ∧ True) ∧ p2)) ∧ p2)))) ∨ ((p1 ∨ (False → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768334412822474795723537224876 : (((p5 ∧ ((((True → p5) → ((p2 → p5) ∨ (p1 → ((p4 ∨ ((p3 ∧ (p3 → True)) → p5)) ∨ True)))) → p5) → ((p1 ∨ p5) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734120974848625143724495413016 : ((((True ∨ p4) ∧ (p3 ∧ ((p5 ∧ (((p5 ∨ True) → p4) ∧ ((p4 ∨ (p1 → p2)) → (p4 → (True ∨ (p5 ∨ p5)))))) ∧ (p3 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190199681054163189252792668221 : (((p3 ∨ (p1 ∨ (((p2 ∨ False) → p3) ∨ False))) ∧ True) ∨ ((((p1 ∨ ((p5 ∧ ((p5 ∧ p1) ∧ True)) ∨ False)) ∧ (p2 → p4)) ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64756873809068184052436381114 : ((p2 ∨ (((p3 ∨ p4) ∧ (((True → True) → (((p3 ∧ ((False → p3) ∨ p1)) ∧ (p5 ∧ (p2 ∨ False))) → False)) ∧ (p1 ∨ p4))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167806171538016604308376789245 : (((((p2 ∧ False) ∨ ((p1 ∧ (p2 ∨ p5)) ∧ p2)) → p1) ∧ ((p5 → (False ∧ False)) ∧ p5)) → ((p4 ∧ ((True ∨ (p1 → p3)) ∧ p3)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173114774139034083796764376680 : ((p2 ∨ ((((p2 ∨ ((p5 ∧ p2) ∨ False)) ∨ p4) ∨ (p3 ∧ p4)) ∨ (p4 → p2))) ∨ (False → (True ∧ ((p3 ∧ (False → p2)) ∧ (p2 ∧ p4))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348068043972932911757644078811 : (p3 → ((p4 ∨ p2) ∨ (((True ∧ p2) ∨ ((((((((False ∨ p5) ∨ False) ∧ False) ∧ p2) ∨ (True ∨ True)) ∨ (p2 → False)) → False) → False)) ∨ p1))) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((((((False ∨ p5) ∨ False) ∧ False) ∧ p2) ∨ (True ∨ True)) ∨ (p2 → False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165679380466450526737359703362 : ((((p5 → ((p1 → p1) ∨ True)) ∨ False) → ((True → (p4 ∨ p3)) ∨ ((p3 ∧ p3) → p3))) ∨ ((p1 ∨ ((False ∧ (p5 ∨ p1)) ∧ p4)) → p5)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40593166848075417652425862576 : (((((p4 ∧ ((p2 → p5) → (((p3 ∧ ((False ∨ p4) ∧ ((p4 → False) ∨ p1))) → ((p4 → p5) ∧ True)) ∨ p2))) ∧ p1) → p5) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40239182236630687055809718004 : ((((p4 ∧ (((p2 ∨ (False ∨ (((p3 ∧ ((((p1 → (p5 → p2)) → p3) → p5) ∨ p5)) ∨ p4) ∧ True))) ∨ True) → p1)) ∧ p4) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337856213318162759839561898233 : (p1 → (((p1 ∧ ((True ∨ p4) ∨ ((p1 ∨ p3) ∨ ((p2 → True) ∨ p2)))) → p4) ∨ (((True ∨ False) ∧ p2) ∨ ((p1 ∨ p4) ∨ (p2 ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117454028724082100696984627450 : ((p1 ∧ (((p2 ∧ p3) → p4) → ((p1 → ((p5 ∧ p1) → ((True → ((True ∨ p4) ∨ (p5 → True))) ∧ p3))) → (p4 ∨ p2)))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707452771533578749073103027452 : (((((p5 ∧ (True ∧ p4)) ∧ ((p3 ∨ p5) ∧ True)) ∨ (p5 ∨ (p4 ∧ (((((True ∨ p5) ∧ p1) ∨ p3) ∧ (False ∧ (p2 ∧ p1))) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326219486013842911594448601046 : (p5 ∨ (p3 → ((((p3 ∧ ((((((p5 → (((False → p3) ∨ p2) ∨ p2)) → p4) → p2) ∨ p2) ∧ False) → p5)) → False) ∨ (True ∧ True)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57632165978511204751706720874 : ((((p3 ∧ p4) ∨ p4) → (((False ∧ False) ∨ (p3 ∨ ((p1 ∨ (p3 ∨ (False ∨ ((p1 ∨ p2) ∧ True)))) ∧ (p5 ∧ p4)))) ∨ (True ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773663864835505856463148169727 : (((False ∨ ((p1 → (((p1 ∧ p2) → (((p5 → (p1 → p1)) ∨ p1) → (p4 ∨ p1))) → (p1 ∧ ((p3 ∨ p5) ∨ (False ∨ False))))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52887257587041604720371676648 : (((p2 ∨ ((p1 ∧ (p2 ∨ (p1 → (True ∧ ((p3 ∧ p4) ∧ p5))))) → p1)) → (True → ((p5 ∧ (p1 → p3)) → ((p5 → p4) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16761303125349963997147642185 : (((((((((p2 ∨ p5) ∨ p4) ∧ (True ∧ False)) ∧ True) → p1) → p5) ∧ ((p4 ∧ True) ∨ ((True → p4) ∧ True))) ∨ ((p2 ∨ False) → p2)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599061556801402910391938408752 : (((((p5 ∨ p3) ∧ (p5 → ((p4 ∨ (p4 ∨ True)) ∧ (p5 → ((((p4 ∧ p5) ∧ (p1 ∧ p3)) → p1) ∧ ((p5 → True) ∨ p1)))))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135760191054886072716935340999 : (((p2 ∨ ((p4 ∨ True) → (p3 ∨ ((((p4 ∨ p2) ∨ p3) ∧ False) ∨ p1)))) ∨ ((p5 ∧ False) → (p5 ∨ (p3 ∨ p2)))) ∨ ((p1 → False) → p5)) := by
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
theorem thm_5_vars_157507467611152698708330101833 : (((False ∧ (p4 ∧ (p3 ∧ (p3 ∨ (p5 ∧ (p3 → (((p3 ∧ False) ∧ True) → p1))))))) ∨ (p5 ∧ False)) ∨ (p3 → (p1 → ((p1 ∨ p1) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69117107053519654640049689479 : ((p5 → ((((p4 ∧ (p4 → True)) → (p3 ∧ p3)) ∧ ((p3 ∧ False) ∧ (p3 ∧ ((((True ∧ p3) ∧ False) ∧ False) ∨ True)))) ∨ (True ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312129657996094117560503855372 : (p2 ∨ (True → ((((p3 → (p4 → (p4 ∧ p2))) → ((p2 ∨ True) ∧ p2)) → p2) ∨ (((((p5 ∨ (p5 ∨ False)) ∧ False) ∨ True) ∨ p3) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_234045784851102287906685920117 : ((p5 ∨ (p2 → p5)) → ((True → ((p3 ∧ (((p4 → p1) ∧ ((False ∧ (False ∨ (p3 → (False → p3)))) → p4)) ∨ p4)) ∧ (p5 ∧ p4))) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234503225807297167156869729366 : ((p2 → (False → False)) → (True ∧ (((((p4 → (p5 → p5)) ∧ (p4 → p3)) ∨ p1) ∨ (p3 ∨ (p2 ∨ (p3 ∨ (True ∧ (p1 ∧ p5)))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67838221077473069372122499239 : ((p2 → (((((p3 → (p3 ∧ (((p3 ∨ ((p5 ∨ (p3 ∧ p1)) → p4)) → (p3 ∨ True)) ∧ p5))) ∨ False) → p5) → p3) ∨ (p2 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185506615965369141321484626438 : ((p2 ∨ (False ∧ ((((p1 → p2) ∨ p5) ∨ (p1 ∧ p5)) → False))) ∨ (((p5 → ((False → p4) → ((p4 ∨ p5) ∧ False))) ∧ (p3 ∧ p4)) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642933752669783202465173179018 : ((((p2 ∧ ((((True ∧ ((p1 ∨ (p2 → p1)) ∨ False)) ∨ (((p3 ∨ p4) → p5) ∧ False)) ∧ p3) → ((p5 ∨ p3) → (p1 ∧ True)))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323984082939713207718298216474 : (p5 ∨ (((p1 ∧ (p5 ∨ (True ∨ ((p4 ∨ False) ∨ (p3 ∨ (False → p1)))))) ∨ p3) ∨ (p5 ∨ ((((p3 ∨ (True ∧ p4)) ∧ p3) ∨ True) ∨ p2)))) := by
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
theorem thm_5_vars_640305028755941144671828507160 : (((((p4 ∨ (p1 ∧ p4)) → (True ∨ (((((((True ∧ p3) ∧ p3) ∨ False) ∧ p2) ∨ p2) → (p1 ∨ ((p4 ∨ False) ∧ p1))) ∨ True))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190706617472474004748368589025 : ((((((p2 ∨ False) ∧ p2) ∨ p2) → p3) ∧ (p1 ∨ p5)) ∨ (((((((p1 ∨ (False → p1)) ∧ False) ∨ True) ∨ p1) → (p2 ∧ p1)) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631223482612812965404405373875 : (((((((p4 → (p3 → ((p5 ∨ ((((((p1 → p3) ∨ p1) ∧ False) ∧ False) ∧ p2) ∧ p5)) ∧ p2))) ∨ (p1 → p4)) → p4) → p1) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329255360641625244323333604444 : (True → ((p5 → (p4 → True)) ∧ (False ∨ ((p5 ∨ True) ∧ (((p1 ∨ (p3 ∧ p5)) → ((p5 ∧ p1) ∨ p4)) ∨ (p1 → (True ∨ (p1 ∨ p4)))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146620049937880217756442828641 : ((True → (p5 → ((((p5 → False) ∧ ((p1 → p1) ∧ (p3 → p5))) ∧ ((p1 ∧ p5) → (p2 ∨ False))) → p1))) ∧ (((p1 ∧ p4) ∧ p3) → p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h10 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h11 := h6 h10
  -- False on the left can always be used.
  apply False.elim h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h12.left
  let h14 := h12.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h13.left
  let h16 := h13.right
  -- One of the premise coincides with the conclusion.
  exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164954844093736045469366657521 : (((((p4 ∨ p1) → ((p3 ∧ ((p3 ∧ p5) → p3)) ∧ ((p2 → p4) ∨ p1))) → True) → p5) ∨ (((True ∧ p2) ∨ True) ∧ (p3 ∨ (True ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44736941529948023657530260122 : (((((p2 ∧ p4) ∨ (p3 → True)) ∨ ((((p1 ∨ True) ∧ p4) → p1) ∨ (((p2 → p1) ∨ p3) ∨ (False → ((p2 ∨ True) → p1))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134228394195782509968814061770 : (((((p3 → p2) → (p3 ∨ (False → p4))) → ((p3 ∧ ((((False ∨ p1) → p3) ∨ p2) ∨ (False → p4))) ∧ p2)) ∨ p3) ∨ ((p1 ∧ p1) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41573905906481163252098740575 : ((((((p4 → True) ∧ ((p4 ∨ True) ∨ p1)) ∧ True) ∧ ((((p2 ∨ ((p4 ∧ p1) ∧ True)) → p5) → ((p2 → p1) ∧ p5)) ∨ True)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47577067164661186126305532581 : (((p1 → ((p4 ∨ ((p4 ∨ p4) → ((p1 ∧ p2) ∧ p1))) → (p3 ∧ (((p4 → (p4 → p5)) ∧ p4) ∨ (p2 → p1))))) ∨ (p1 ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194060000227214038954221034913 : ((p5 ∨ (False → ((True ∨ ((p3 → p3) ∨ p5)) ∨ p1))) → (p4 ∨ (((((p3 ∧ p5) ∨ ((p4 → p5) ∧ False)) ∨ p5) → (p5 ∧ False)) ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248182827370912818357141113375 : ((p2 ∨ False) ∨ (p4 ∨ ((((True ∨ ((p1 ∨ p5) ∧ p1)) ∧ p2) ∨ False) ∨ ((((p3 ∧ (p3 → p2)) → p3) ∨ (p2 ∨ (True ∨ p5))) ∨ p2)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157190451837452425172345360943 : ((((p5 → (False → (((p4 ∧ p2) → p5) ∨ (((False ∨ p5) ∧ (True ∨ p2)) ∨ p1)))) → p2) → p4) ∨ (True ∧ (((False ∨ p2) ∨ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133697353783231690942150040158 : (((((p1 ∨ p5) ∨ (False ∨ ((p1 ∨ ((True → p3) → p1)) ∧ (True → (p4 ∧ False))))) → ((p2 → False) → p5)) ∧ p3) ∨ (False → (p2 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356727399896338801196573806542 : (p5 → (((p1 ∨ (p3 → p5)) ∧ (p1 ∨ p2)) ∨ (((((p3 ∧ (True ∧ (p1 ∨ p5))) ∨ p2) ∨ True) ∨ p5) ∨ (True → ((p3 ∧ p1) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54997009532760256601924733813 : ((((p5 ∨ p5) ∨ (p2 ∧ (p5 ∧ p2))) ∧ (((p5 ∧ p2) ∧ p2) ∨ (((((False ∧ p4) ∨ (p2 ∧ (False ∨ p2))) ∧ False) ∨ p2) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47127077424570780539008410379 : ((((((((p5 → p5) ∧ (p1 ∧ p1)) ∧ True) ∧ (True → True)) ∨ ((p4 → False) ∧ (True → p5))) → (True → (p3 ∨ p5))) ∨ (p1 → True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205298622442317635616006334244 : (((p5 ∧ (p5 ∧ p4)) ∨ (True → p1)) ∨ (((p4 → True) ∨ p3) ∧ ((((True ∧ (p3 ∧ p2)) → (p3 ∧ True)) ∧ (p4 ∧ (p1 → p2))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_336374954045944987961999982643 : (p1 → ((True ∧ (((p3 → p1) → (((p3 ∧ ((p4 ∧ p2) ∧ True)) ∨ p3) ∧ ((p4 → p4) → False))) → (((p4 → False) ∧ p2) ∧ p4))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p3 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : (p4 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h8
  -- False on the left can always be used.
  apply False.elim h10
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h11 : (p3 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h12
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h13 := h2 h11
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
  have h15 : (p4 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h16
    -- One of the premise coincides with the conclusion.
    exact h16
  -- We have shown the premise of h14, we can now drive its conclusion.
  let h17 := h14 h15
  -- False on the left can always be used.
  apply False.elim h17
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h18 : (p3 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h19
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h20 := h2 h18
  -- We need to get the right conjuct of h20 based on <expert-advice>.
  let h21 := h20.right
  -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
  have h22 : (p4 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h23
    -- One of the premise coincides with the conclusion.
    exact h23
  -- We have shown the premise of h21, we can now drive its conclusion.
  let h24 := h21 h22
  -- False on the left can always be used.
  apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345548094103387337231874965632 : (p3 → ((((p4 → (p5 → p3)) → (False ∨ p2)) ∨ (p5 ∨ ((p1 ∨ ((p4 → ((p4 ∨ True) ∨ (p5 ∨ p1))) → (p3 → True))) ∨ p2))) ∨ p2)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



