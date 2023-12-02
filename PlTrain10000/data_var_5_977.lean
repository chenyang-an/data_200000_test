variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160829004418017656586828153002 : ((((p4 ∨ p4) → (p2 ∧ (p1 ∧ False))) → (p3 ∧ (p1 → (((p4 → (p4 ∨ False)) ∧ p3) ∨ True)))) → (((p1 ∨ True) → False) ∨ (True ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351942336388710872380619394814 : (p4 → (((p1 ∧ p2) ∧ ((p3 → ((p1 ∨ p1) ∧ False)) ∧ p3)) → (((p5 → ((p4 ∧ p4) ∨ p2)) ∨ ((p1 ∨ p2) → (p5 ∨ p3))) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h6.left
    let h10 := h6.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h11 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h12 := h9 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h2.left
    let h16 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h16.left
    let h20 := h16.right
    -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
    have h21 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h20
    -- We have shown the premise of h19, we can now drive its conclusion.
    let h22 := h19 h21
    -- We need to get the right conjuct of h22 based on <expert-advice>.
    let h23 := h22.right
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175438238530012478262552998763 : ((p1 → (((p2 ∨ p4) ∨ ((p2 ∧ (p5 ∧ (p3 ∨ p3))) → p2)) → (p4 ∧ p5))) → (p5 → (p1 → (p4 ∧ (((p5 ∧ True) ∧ p5) → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((p2 ∨ p4) ∨ ((p2 ∧ (p5 ∧ (p3 ∨ p3))) → p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h14 := h5 h6
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- One of the premise coincides with the conclusion.
  exact h15
  -- Implications on the right can always be decomposed.
  intro h16
  -- Conjunctions on the left can always be decomposed.
  let h17 := h16.left
  let h18 := h16.right
  -- Conjunctions on the left can always be decomposed.
  let h19 := h17.left
  let h20 := h17.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h21 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h22 := h1 h21
  -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
  have h23 : ((p2 ∨ p4) ∨ ((p2 ∧ (p5 ∧ (p3 ∨ p3))) → p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h24
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- Conjunctions on the left can always be decomposed.
    let h27 := h26.left
    let h28 := h26.right
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h29 =>
      -- One of the premise coincides with the conclusion.
      exact h25
    case inr h30 =>
      -- One of the premise coincides with the conclusion.
      exact h25
  -- We have shown the premise of h22, we can now drive its conclusion.
  let h31 := h22 h23
  -- We need to get the left conjuct of h31 based on <expert-advice>.
  let h32 := h31.left
  -- One of the premise coincides with the conclusion.
  exact h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717220355621377061662650885275 : ((((p2 ∨ (p4 ∨ (True ∨ False))) ∧ (False ∨ ((p2 ∨ (((p4 → p1) → ((True ∧ (True → p1)) → (p3 → False))) → p5)) → (p4 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47666177857915561401554781614 : (((((True ∨ ((True → ((p3 ∧ True) ∨ False)) ∨ p3)) ∨ (((((False ∨ p2) ∧ p2) ∧ (True → False)) → True) ∧ True)) ∧ True) → (p5 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750444800174482638823829829178 : (((True ∧ (((p1 → (((False ∧ p2) ∨ p3) → ((p4 ∧ True) ∨ (p5 ∧ True)))) → (((p1 → True) ∧ p2) ∧ False)) ∨ (True ∨ (p4 ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342425796275570440308047199502 : (p2 → (((p2 ∧ ((p3 ∨ p1) ∧ p5)) ∧ ((False ∨ ((p3 ∨ p2) ∨ (p5 ∧ False))) → p5)) → ((((False → False) → (p5 → False)) ∧ True) ∨ p5))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66042200043223825012717581624 : ((p5 ∨ ((True → (((((True ∨ (True ∧ True)) ∨ (p4 → (p4 ∨ p3))) ∨ p3) ∨ ((False ∧ (p4 → True)) → (True → p4))) → p5)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341712832358441700125737860333 : (p2 → (((((((p3 ∧ p3) → False) → p5) → ((p2 ∨ False) ∨ p1)) → False) ∨ ((p3 ∨ (p1 ∨ p1)) → (p5 ∨ (p1 → p5)))) ∨ (p5 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591698363689998601596660367918 : (((((((p5 → p4) → (((False ∧ p2) ∨ ((p2 → p3) ∨ (p5 → (p3 ∨ ((p1 ∧ p4) → p1))))) ∨ p1)) ∨ p2) ∨ (True ∨ p4)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117111764035271749583356489383 : (((p3 → True) → (p3 → (((False ∨ ((False ∧ (p4 → ((p2 ∨ (p4 → True)) → p5))) ∨ (p1 ∨ (False ∨ True)))) ∧ p4) ∨ p2))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259543926479002880838434419201 : ((False → p5) → (p3 → (((((p3 → True) ∧ (((True ∧ True) ∧ (p2 → (p3 → p4))) ∨ ((p3 ∨ p5) ∧ p2))) → False) ∧ p1) ∨ (True ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157841480375335952349109176151 : (((((False ∨ (((False → True) → p1) → p1)) → False) ∨ p5) ∧ (((False ∧ p3) → p5) ∨ (True ∧ p3))) ∨ ((p1 → (p1 ∨ (p4 → p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158790704523185712100463793943 : ((p5 ∧ ((p4 ∧ (((False ∨ ((p2 → p5) ∧ ((p3 → p1) → p2))) → True) → p5)) ∨ (p2 ∧ p1))) ∨ ((p4 → ((p2 → p4) → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62673972403362075178246735072 : ((p4 ∧ ((False ∧ (((((p5 → False) ∧ (True ∧ False)) ∧ ((False → p1) ∧ False)) → (True ∧ p3)) ∧ (p2 ∧ ((p2 ∨ p3) → p4)))) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264006653698763652743286102029 : (True ∧ (((p3 → ((p1 → (p3 → ((True ∧ p5) ∧ p4))) ∨ p4)) → True) → (((False → ((p4 → p4) → ((p3 ∨ p3) ∨ False))) → p2) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117756145756292952531357058461 : ((p4 ∧ ((((((True ∨ (((p4 ∨ p4) → True) → (p1 ∨ p2))) → (p3 ∧ (p4 ∧ p5))) → False) → (False → True)) ∧ p5) → p4)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213448597957893836670827970044 : (((p5 ∨ (p3 ∨ p5)) ∧ False) ∨ ((False ∨ (((p2 ∧ p5) → p2) → (False → ((p1 ∧ ((p4 ∧ (p4 → p2)) ∨ (p5 ∧ True))) → p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238301944846057996141092247210 : ((False ∨ True) ∧ ((p5 → (p4 → ((p2 ∨ (False ∨ ((p2 ∨ ((False ∧ p4) ∨ p2)) ∨ p5))) ∧ (p1 → (p1 → ((p3 ∨ p3) → True)))))) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111979722087205203672672235510 : ((((p1 → (((p1 ∧ p1) ∧ p4) ∨ p2)) ∨ (p1 ∧ (((True → (p5 ∨ True)) → (False ∨ (p3 ∨ (True ∧ True)))) → False))) ∨ p3) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633365325365795364499464089489 : ((((((p1 ∨ ((((p1 ∧ p1) → (p1 ∨ (p2 → ((True → p5) ∧ ((p4 → p3) ∨ False))))) → p2) → p3)) ∨ p3) ∨ (p1 ∨ True)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3917687254416415778392670126 : (False ∨ ((((p4 ∧ (p2 ∨ ((p4 ∨ p2) → (p5 ∨ (p5 ∨ ((True ∨ p4) ∨ (p1 ∧ p1))))))) ∨ True) ∨ False) ∨ (p5 → (p2 → p4)))) := by
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
theorem thm_5_vars_40529831497458031468193752781 : ((((p1 ∨ (((((((True ∨ (p3 ∧ False)) ∧ p2) ∨ p3) → p4) → (p5 ∧ p5)) ∧ ((p3 ∧ True) → p3)) ∨ (p1 ∧ p2))) ∨ p2) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47905245170687084412020015626 : (((((False ∨ (p5 → (((p1 ∨ (False → True)) ∧ (p1 → (True → ((p1 → p5) ∧ p4)))) → p1))) ∨ p2) → (p3 ∧ p4)) → (p2 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_854781974965397083910575944968 : ((((((False ∨ p1) ∨ (((((False ∧ False) ∧ p3) → p4) → ((p4 ∨ p4) → (False ∨ True))) ∨ (False → (p2 ∨ (True ∧ p5))))) ∧ True) → False) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False ∨ p1) ∨ (((((False ∧ False) ∧ p3) → p4) → ((p4 ∨ p4) → (False ∨ True))) ∨ (False → (p2 ∨ (True ∧ p5))))) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175425555102291616890130178599 : ((False → (p3 → ((False ∧ (((p5 ∧ (True ∨ p1)) → p2) ∧ (p4 ∧ p3))) ∧ p1))) → (((p4 → ((p3 → True) ∧ p4)) ∨ p5) ∧ (p4 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726044661726261799700762134725 : (((((True ∧ p4) ∨ p2) ∨ ((p2 ∨ p5) → (((p4 ∨ p5) ∧ p3) ∧ ((False ∨ p5) ∧ (p5 ∧ (((p3 → (p5 ∨ p1)) → False) → p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255866810384475782981973380886 : ((True ∨ p1) → (((((p5 → True) → (p1 → p5)) ∧ p2) → ((((p3 ∨ True) ∨ False) → (p5 ∧ p3)) ∧ True)) ∨ ((False → (p1 ∧ p2)) ∨ p2))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217413583804135177196158397126 : (((p1 → (p5 ∧ p4)) ∨ p1) → (((((p1 ∨ (True → (p5 → (p1 ∧ p1)))) → True) ∧ (True → (p3 ∧ (p1 → p1)))) ∨ False) ∨ (True ∨ p2))) := by
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
theorem thm_5_vars_59331543608546617620747803548 : (((p4 ∨ p4) ∨ (p2 ∧ ((False → ((((True ∨ (((True ∨ p1) → (p3 ∨ p5)) ∨ False)) ∧ (p4 ∧ p3)) ∨ False) ∧ (False ∨ p2))) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_382423050838904752318265957480 : ((((((p3 ∨ ((p5 ∧ p5) ∨ (p5 ∧ (p3 ∨ (False → (p2 ∧ p3)))))) ∧ (p4 ∧ (p3 → (True ∨ ((True ∨ p2) ∨ True))))) ∨ True) ∨ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52901164245465959133684238846 : (((True → (False → (((p1 → (p4 ∨ p2)) ∨ ((p4 → p2) → True)) ∨ True))) → (((True ∨ p3) → (p4 ∧ (p2 → (p3 ∧ p3)))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53038728458168733444819826472 : (((((False → p3) → p5) → ((p4 ∨ p4) → ((p2 ∧ p5) ∨ p3))) ∧ ((((p1 → ((p3 ∧ p4) ∨ p1)) ∧ p2) ∨ p5) → (p3 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201278031542751363098010536854 : ((p3 → (p3 → ((False ∨ p2) ∨ (True → p2)))) → (False ∨ ((((((((p2 ∧ p5) ∧ False) → p2) → p2) ∧ p5) ∧ p2) → p1) ∨ (False → p2)))) := by
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
theorem thm_5_vars_596149594910301362683855272800 : (((((((p2 ∨ (p2 → p1)) → (p1 ∨ True)) ∧ p1) ∧ ((True → ((p4 ∨ True) ∨ (p2 ∧ p5))) ∧ ((True ∧ (False ∧ p2)) ∨ p3))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173413203761334183807065211390 : ((p5 → ((p4 ∨ (p5 → (p5 ∨ (p5 ∧ (p1 ∨ (p2 ∧ (p2 → p2))))))) → False)) ∨ ((p3 ∧ ((p3 ∨ ((p4 ∨ p4) ∧ p3)) ∧ p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41343109547634868920905749581 : (((((((p3 → p1) → p1) ∧ p4) → ((p1 → (p4 ∨ (p4 ∨ p3))) → (p2 ∧ p2))) ∨ ((True → ((False → p2) ∨ p5)) → p2)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148238745021734446637770725882 : (((((p2 → p4) → ((False ∧ ((True ∧ p3) ∧ p1)) ∧ p4)) ∨ ((p5 ∨ p4) → True)) ∨ (p5 ∧ (True ∧ True))) ∨ (((p4 ∨ p3) ∨ p4) ∨ p4)) := by
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
theorem thm_5_vars_157618139509837262546781747627 : ((((p4 ∨ (((True ∨ (p3 ∨ p3)) ∧ (False → p2)) ∧ p3)) ∧ (p2 ∨ False)) ∧ (p1 ∨ (p3 ∧ False))) ∨ ((((True → True) ∨ p5) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810166702251206611028546818311 : (((p5 → ((False ∨ (((p1 ∧ (p2 ∧ (True ∨ (p5 ∨ ((p1 ∧ p5) → False))))) ∨ False) ∧ p3)) ∨ ((False → ((p3 ∨ p2) → p4)) ∨ p4))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51160037089997959701047728693 : ((((p5 → ((p4 → (p3 → p1)) → ((True → (p2 ∨ (True ∨ p4))) ∧ (p4 → p1)))) → p5) ∨ ((p4 ∧ p2) → ((p4 ∧ True) ∧ True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116281746138823169074020976622 : (((p1 ∨ (p5 ∧ p2)) ∨ (True ∧ ((p2 ∨ (p3 ∨ False)) → ((p3 ∧ (p2 ∧ (p1 ∨ ((p5 ∧ (True → p3)) → p2)))) ∨ p4)))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261118174302724004808317235892 : ((p4 → p3) → (p4 ∨ (((((p1 ∨ ((p3 → p5) → True)) → ((p2 ∧ (p1 → True)) ∧ False)) ∨ False) ∧ p4) → ((p3 → p4) ∧ (False ∧ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h2.left
  let h9 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : (p1 ∨ ((p3 → p5) → True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h11
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15
  -- Conjunctions on the left can always be decomposed.
  let h16 := h2.left
  let h17 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h18 =>
    -- One of the premise coincides with the conclusion.
    exact h17
  case inr h19 =>
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260603841881430206565054415802 : ((p3 → p2) → (((p3 → False) → (p4 ∧ (((p3 ∧ (p1 → False)) → ((p2 ∧ p3) ∧ p2)) ∧ (False ∧ p2)))) ∨ (((p1 ∧ p4) → p5) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614042603135281230248889449598 : ((((((False → p2) → (((True → (((True → p1) ∧ p1) ∨ p1)) → (p5 ∨ p2)) ∨ (p2 → (p2 ∧ p3)))) ∨ (p5 ∨ (p3 ∧ p4))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324377104426609232505220363947 : (p5 ∨ ((p1 ∧ (False ∧ ((False ∨ p4) ∧ False))) ∨ ((False ∧ True) → (True ∨ ((True ∧ p1) ∨ (((p3 ∧ True) ∧ p2) ∧ (p2 → (False ∨ p2)))))))) := by
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
theorem thm_5_vars_258143444926413553990083645006 : ((p4 ∨ p3) → (p5 ∨ ((True ∨ True) → ((p4 ∧ (p4 ∨ (p5 → p1))) ∨ (((p2 ∨ (False ∧ p4)) → (p3 ∨ (True ∧ (p3 ∧ p2)))) ∧ p3))))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h9
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- False on the left can always be used.
        apply False.elim h12
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h15
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- False on the left can always be used.
        apply False.elim h18
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234620258886721507639947751819 : ((p3 → (False → True)) → (((p1 ∧ p2) → (False ∨ (((False ∧ (p3 ∧ False)) ∨ p3) ∨ (p3 ∨ (p2 ∨ p2))))) ∧ (((False → p5) → True) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232172770149088767106887782589 : (((True → p5) → p4) → (((p5 ∧ p4) ∨ p5) → (((p3 ∧ (p2 ∨ (p5 → False))) ∧ ((True ∨ (((p2 ∨ True) ∨ p3) ∧ p5)) → p3)) ∨ p4))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : (True → p5) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h9 := h1 h7
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33349466861615516726867481057 : ((p4 ∨ ((((((True ∨ p4) ∧ (p2 ∨ p1)) → ((((p5 ∧ p5) → p4) ∧ True) ∧ p2)) ∨ ((True → False) ∨ p5)) ∧ p2) ∨ (True → True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_48559548699013492373244571902 : ((((((p5 → ((p1 ∧ ((p2 ∧ (p2 ∨ p2)) ∨ p5)) ∨ p1)) ∨ True) → ((p3 ∧ p3) ∨ (p2 ∧ False))) → p3) ∧ (False → (p5 → p5))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 → ((p1 ∧ ((p2 ∧ (p2 ∨ p2)) ∨ p5)) ∨ p1)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809977354333661301160212369663 : (((p5 → ((p2 ∨ ((((False ∨ (((True ∨ ((p5 ∨ True) ∨ p4)) ∨ (True → p5)) ∨ True)) ∨ p2) → True) → p2)) ∨ ((p5 ∨ True) ∨ True))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_164741339476083798271841851309 : ((((((False ∨ ((False ∧ (p4 ∨ p4)) → (p1 → True))) ∧ p2) ∧ False) ∨ (p4 ∨ False)) ∨ p1) ∨ (True ∨ (p4 ∨ (p4 → (p3 ∧ (p4 ∧ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329154192111895658103949220207 : (True → (((True → (p1 → p4)) ∨ p1) → (p3 → (((True ∨ p1) ∧ (((p1 ∧ True) ∨ (p2 ∨ ((p3 → p2) ∨ p5))) ∧ (p4 ∨ p2))) ∨ p3)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67842065462611367888107762437 : ((p2 → ((((False → (p3 → p2)) ∧ p1) ∧ (True → ((False ∧ ((p5 → False) → p1)) ∧ ((p1 ∧ (p3 → p1)) ∧ p5)))) ∨ (p4 → p2))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_527227661823932791736413679 : (((((p4 ∧ (((((((p1 ∧ False) → ((p2 → p3) → p1)) ∧ p1) → p4) ∨ p1) ∧ True) ∧ True)) ∨ (p3 → False)) ∧ True) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358122981596014449100877495086 : (p5 → (p2 ∨ ((((p3 ∨ p4) ∨ p3) → p2) ∨ ((p5 → p1) ∨ (((p2 ∧ (True ∨ (p4 ∨ ((p2 ∧ p3) ∨ p4)))) ∨ p3) ∨ (p5 ∧ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309661541781889740481299178386 : (p2 ∨ ((p3 → ((p1 ∨ ((((p4 ∧ ((p5 → p2) → p2)) ∧ p1) ∨ p4) ∨ (p3 ∨ (p5 → p5)))) ∧ (p5 ∧ True))) ∨ ((p4 → p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354854185584781258554503827207 : (p5 → (((True ∧ p5) → ((p2 → p5) → (((p2 ∨ (((((p3 ∧ (p2 → (p2 → False))) ∨ True) ∨ p2) ∧ p4) ∧ p4)) → p2) ∧ p1))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310399543388202053023998915646 : (p2 ∨ (((False ∨ False) ∨ (p1 ∧ ((True ∨ p3) ∨ p2))) ∨ ((p5 ∨ (False → ((p5 → p1) ∨ ((False ∧ p3) ∧ (p4 ∨ p2))))) ∨ (False ∨ False)))) := by
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
theorem thm_5_vars_54855742744078785778743163256 : ((((((p2 → p5) → p1) → p2) ∧ p3) ∧ ((p5 ∧ (p3 ∧ (((p2 → p3) → (p5 ∧ p5)) → (p2 ∨ p5)))) ∧ ((False ∧ p3) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299320801241284926256800902017 : (False ∨ (((((p4 → p3) → p3) ∧ (p1 → p5)) → (((p4 → p3) → ((False ∨ (p5 ∧ True)) ∨ (((p3 ∧ p1) → True) ∧ p4))) → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19045720739738088688317469304 : (((((p1 ∨ ((((p3 ∧ p5) ∧ p4) → (p2 ∨ p3)) ∨ p2)) ∨ ((p1 → p2) ∨ p1)) → p4) → (p4 ∨ (False ∨ (p5 ∧ (p2 → p4))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∨ ((((p3 ∧ p5) ∧ p4) → (p2 ∨ p3)) ∨ p2)) ∨ ((p1 → p2) ∨ p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352772215109378640805457093194 : (p4 → ((p4 ∧ p5) → (((p5 ∨ (True → ((p4 → p1) ∧ True))) ∧ ((((p3 ∨ ((p1 ∧ p3) ∨ p2)) ∧ p4) ∨ (p5 → p2)) ∧ False)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166442633645863004995957464930 : ((p2 ∨ ((((p3 ∧ p5) ∧ ((p4 ∨ (False ∧ (p2 ∨ p2))) → p2)) → (p2 ∨ p2)) ∨ True)) ∨ (True → ((False → p1) → ((p1 → p2) → p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135854901369828336873300246895 : ((((p3 ∨ ((p2 ∧ (p1 ∧ ((p4 → p2) ∧ p4))) ∧ True)) ∧ False) ∨ (p1 ∨ (((True ∨ p1) ∨ (p2 ∨ p4)) ∨ p4))) ∨ ((p4 → True) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217072949812885730643343788944 : ((((p4 → False) ∧ p4) ∨ True) → ((False ∨ (((((p1 ∧ p4) ∨ (p2 → (p2 ∧ p1))) ∧ (p3 → (p1 → p5))) ∧ p2) ∧ (p5 ∧ p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653010610353694065936462895287 : ((((p5 ∨ (p2 ∨ ((((p5 ∧ p5) ∨ ((p5 ∧ (((p4 ∨ (p4 → p3)) → (True → True)) → True)) → p1)) ∧ p2) ∨ p2))) ∧ (p1 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186448572194136322197498522945 : (((((p3 ∧ (p1 → True)) ∧ (p3 ∧ p1)) ∧ p4) ∧ (p5 ∨ p5)) → (p2 ∨ ((False ∧ (False ∨ p1)) ∨ (False → ((False → (False ∧ False)) → p2))))) := by
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
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h7.left
  let h11 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Implications on the right can always be decomposed.
    intro h14
    -- False on the left can always be used.
    apply False.elim h13
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Implications on the right can always be decomposed.
    intro h17
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158446530851896545365975131259 : (((p4 ∨ False) ∨ (True → ((False ∨ ((p3 ∨ p2) ∨ p4)) ∨ (((p3 ∧ True) ∧ (False → False)) ∧ p4)))) ∨ (p5 → ((p3 ∨ p3) → (p3 ∨ p1)))) := by
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
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244667231330020923199045478505 : ((False ∧ p5) ∨ (p5 → (p4 ∨ (p5 → (False ∨ (p2 ∨ (p5 → ((p3 → p5) ∨ ((False ∨ False) ∧ (p1 → (((True ∧ True) ∨ p4) → p2))))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338605219258933185418426200798 : (p1 → ((p1 ∧ (p2 → True)) → (True ∧ ((p3 ∧ p4) → (p2 ∨ ((True → ((p1 → (p3 ∨ ((p5 ∨ False) ∧ p1))) ∧ (p2 ∧ p1))) → p2)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h8
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750291050954359010752388523049 : (((True ∧ ((False ∨ ((((True ∨ (p3 → True)) ∧ (True ∨ (p1 → p4))) → (p3 ∧ (((p5 ∧ p4) → True) ∧ False))) → p5)) ∨ (p2 → p1))) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∨ (p3 → True)) ∧ (True ∨ (p1 → p4))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51491433884638502864294894219 : (((((p3 ∨ p3) → (True ∧ p5)) ∨ (p2 → ((((p1 ∧ p2) ∧ True) ∨ (True → p5)) → p5))) → ((p2 → (p2 → (True ∧ p5))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113304325319475201047798641493 : ((((((p2 → p2) ∨ p3) ∧ p2) ∧ (((p4 → False) ∧ ((((p3 → False) → p1) ∧ False) ∨ (False → p3))) ∨ p3)) ∧ (p3 ∧ p4)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684131852947645465448256814370 : (((((True → ((p2 ∧ (False ∧ (False ∨ True))) ∧ (False ∨ ((p2 ∧ p4) ∧ p4)))) ∧ (p2 ∧ p5)) ∨ (((p3 ∨ p3) ∧ (True ∧ False)) → p3)) ∨ p1) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171275742402071453753764203214 : ((p5 → ((p5 ∨ ((((False ∧ p3) ∨ p1) → False) ∧ p5)) → ((False → p3) ∧ True))) ∧ (p2 ∨ (((True ∨ (p5 ∨ (p4 → False))) → False) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42347477108050300594365889505 : (((p3 ∧ ((p1 → ((p4 ∨ (p2 → ((p5 ∧ True) ∨ (False ∨ p5)))) → p3)) → ((p2 ∨ True) → ((p3 ∨ (p5 ∨ p5)) ∨ p5)))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737805283532603953734882542833 : ((((True ∧ False) ∨ (((True → ((False ∧ (p5 ∨ (p3 → p4))) → (((p4 → p4) ∧ True) → (p5 → True)))) → p3) ∨ ((False → p4) → True))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_64807439798910522840628849437 : ((p2 ∨ ((p1 → ((((True ∨ p1) ∧ (p3 ∨ p2)) ∨ (False ∨ True)) → (((p4 → False) ∧ (p1 ∧ ((p5 → True) ∧ p1))) ∨ p1))) ∨ p1)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156867333780839283566026597498 : ((((((False ∧ p2) ∧ p4) ∧ (p3 → ((p3 ∨ p4) → (False ∧ ((p1 ∧ p1) ∧ p4))))) ∧ p2) ∨ True) ∨ (((p1 ∨ p5) ∨ (False ∧ p2)) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115274109322992950396480095098 : (((p1 ∨ ((False ∧ ((p2 ∧ p2) ∨ (False ∨ p4))) ∧ True)) ∨ (p3 ∨ (p3 ∨ ((p1 ∧ (p1 ∨ (p4 ∨ p1))) ∧ (p3 ∨ p5))))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39174081538264510173069656349 : ((((False → False) → (p5 → ((p1 ∨ (p5 → ((False ∨ p3) ∧ False))) ∨ (((p1 → (p4 ∧ p5)) ∨ ((False ∨ False) → p1)) → True)))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187189335454075430092211255191 : (((True ∨ False) → (((False ∧ p4) ∨ (p5 ∨ (p4 ∧ p2))) → False)) → (p1 ∨ (((p4 ∧ p4) ∨ p4) ∨ ((((p2 → p4) ∧ p2) ∧ p4) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (True ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : ((False ∧ p4) ∨ (p5 ∨ (p4 ∧ p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177841882645180943385366149273 : (((((p4 ∨ True) ∧ ((p5 ∨ (True ∧ True)) ∧ (p5 → p3))) ∧ p4) ∨ p2) ∨ ((p2 ∨ (p4 ∨ False)) → ((True ∧ (True ∧ (p4 ∧ p1))) ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46623533157898734167907298102 : (((p4 ∧ (((True → (True ∧ (((p4 → p5) ∨ ((p4 → (p4 ∨ (p2 → (False ∧ False)))) ∧ False)) ∨ True))) ∧ p4) ∧ p3)) ∧ (p5 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660857345590758791767758242385 : (((((p4 ∧ (False ∧ ((p1 ∨ ((False → (p4 → ((p1 ∧ p1) → p1))) ∧ True)) → (p1 ∧ (p2 ∨ (p5 → p3)))))) → p4) → (True → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117803756342197611472288986827 : ((p4 ∧ ((True ∨ (p4 ∨ (p2 ∨ False))) → (((p4 ∧ ((((p3 → False) ∧ True) → ((p1 → p4) ∨ p3)) → p4)) ∧ p2) ∧ p1))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225725340057412544621052335254 : (((p4 → False) ∧ False) ∨ (((p1 → (p2 → p3)) ∧ (False ∨ (((p4 ∨ p2) ∨ p1) ∨ p2))) ∨ ((p4 ∨ ((True → p3) ∨ True)) → (True ∧ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700980288121719991225641674209 : (((((False ∨ ((p2 → (p2 → (p4 → p1))) → p2)) ∨ True) ∧ (True → ((((True ∨ ((p2 → p1) ∧ (p3 ∨ p1))) ∨ p3) → True) → True))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131032390469988033941989750004 : (((((p4 ∨ p4) ∨ p3) → (p2 ∨ ((False ∨ p4) ∧ p4))) ∨ ((((p1 ∨ (p1 → (p5 ∧ p5))) ∨ p1) ∧ p3) ∨ True)) ∧ (p5 ∨ (p2 ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337393697303722437234284519706 : (p1 → ((p3 ∨ ((((p2 ∨ True) ∧ (False ∨ p4)) ∧ (p1 ∨ ((p4 → p3) → True))) ∧ (p2 ∨ (p1 ∧ (p2 ∨ p4))))) ∨ ((p2 → True) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68629385705779429652468360975 : ((p4 → ((False ∨ (p2 ∨ (((True → (((p2 → p4) → ((p1 → (p2 ∨ (p3 ∨ (p5 ∧ p1)))) ∨ p4)) → p2)) ∨ p4) ∨ p2))) ∨ p3)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641632997831999925918147580501 : (((((True ∨ True) → (p1 → (((((((p2 ∨ (p2 ∨ p4)) ∧ ((p2 ∨ False) ∧ (p1 → p1))) ∨ p4) ∧ p1) ∧ p2) ∧ True) → p4))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262362233066203703933218321846 : (True ∧ (((p4 ∧ (p4 → p5)) ∨ ((p3 → ((p2 ∨ p1) → (False ∨ (p3 → p4)))) ∨ (((True ∧ p3) → p3) ∨ (p5 ∧ (p3 → p3))))) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65794758935015911039070004124 : ((p4 ∨ (((True → (p1 ∧ (((p1 ∧ p3) → True) → p1))) → p4) ∧ ((p5 ∨ (p2 ∧ ((((True → p2) ∨ False) → p5) ∧ p4))) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53404291138668196697516777605 : ((((p3 ∨ ((((True → False) ∧ p4) → p1) ∧ p4)) ∨ (p1 → False)) → (((((p3 ∧ False) ∧ False) ∨ (p4 ∨ (True → p4))) ∨ True) ∨ p4)) ∨ p2) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684391336309493338918086090606 : ((((((p1 ∨ ((p1 ∧ (False ∨ p3)) ∧ p5)) ∨ (p1 → p2)) → ((p5 → p2) ∧ (p5 → p1))) ∨ (p1 ∧ (p4 ∧ ((p4 → p3) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321291243204665285021712808818 : (p4 ∨ (p5 ∨ ((((p1 → (True ∨ (((p3 → (p5 → p3)) ∨ (((p1 ∨ False) ∨ p3) ∨ p4)) ∧ p3))) → ((True → False) ∧ p5)) ∧ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54541876079392884988034922671 : ((((p4 → p2) → ((p1 → p2) → (p1 ∨ p5))) ∨ (True → ((p4 ∨ p5) ∨ (((p5 ∨ (True → (p1 ∧ p5))) → (False ∨ p4)) ∨ True)))) ∨ p5) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



