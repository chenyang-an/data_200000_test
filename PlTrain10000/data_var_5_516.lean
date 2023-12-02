variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200806393168135765711121850927 : ((p5 ∧ ((p4 ∨ (p2 → (p5 → p2))) → False)) → (((((p3 → (((p4 ∨ p5) → True) ∨ p5)) ∨ p1) → p2) ∧ p2) ∨ (p3 ∨ (p3 ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p4 ∨ (p2 → (p5 → p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h4
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144747673804010597818685071038 : (((((False ∧ (p4 → p4)) ∧ ((p1 ∧ (((p3 → p2) ∨ False) ∧ p3)) → False)) ∧ p3) ∨ (p3 → (p2 ∨ True))) ∧ (p4 ∨ ((p4 ∨ p1) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53452952188279817902663133437 : ((((True ∨ True) ∧ ((p5 ∨ p3) → ((p3 ∧ (True ∨ p5)) ∧ False))) → (((p2 → (p5 ∧ ((False ∨ p2) → (p5 → False)))) → False) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68599486893649463736943021350 : ((p4 → (((p1 ∨ (((p5 ∨ p4) ∧ ((((p1 → p5) → (p5 ∧ p2)) ∨ p5) ∨ ((p1 ∧ False) → (False ∨ False)))) ∨ p3)) ∧ False) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316959251711318130397295771139 : (p3 ∨ (p2 → (p4 ∨ (((p3 → p2) → (p5 ∨ p5)) → (p2 → (p1 ∨ ((p4 → p1) ∨ ((p1 → (p1 ∨ ((p4 ∧ p4) → p3))) ∨ p5)))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165828451003885803304875277594 : (((p1 → (p4 ∧ False)) ∧ (p5 ∧ (p1 ∨ (False ∧ ((p2 ∨ ((False ∨ p4) ∨ p4)) ∨ p5))))) ∨ (True ∨ ((((p5 ∨ p3) ∨ p3) → p5) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774881457897480205034899277358 : (((False ∨ ((True → (p1 ∨ (p3 ∧ p2))) ∨ (((p4 → (p1 ∧ (True → p3))) → (p1 ∨ True)) ∨ (False ∨ (((p2 ∧ False) → p4) → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_494764829133281610280551506290 : (((((p1 → p1) → (False ∧ p5)) → (((((p3 → True) ∨ p4) → p3) ∨ (p5 ∨ ((p3 ∨ p4) → False))) ∧ (False ∨ (p5 ∨ (p5 → p3))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (p1 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h6
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_405155119255541522630256243407 : ((((((((((p4 ∨ p3) → ((p4 ∨ (p5 ∨ p2)) ∧ False)) ∧ False) → p4) → False) → (p2 ∧ (True ∧ (p2 ∧ (p2 ∧ p2))))) → False) → p5) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((((p4 ∨ p3) → ((p4 ∨ (p5 ∨ p2)) ∧ False)) ∧ False) → p4) → False) → (p2 ∧ (True ∧ (p2 ∧ (p2 ∧ p2))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((((p4 ∨ p3) → ((p4 ∨ (p5 ∨ p2)) ∧ False)) ∧ False) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h4
    -- False on the left can always be used.
    apply False.elim h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : ((((p4 ∨ p3) → ((p4 ∨ (p5 ∨ p2)) ∧ False)) ∧ False) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h12
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h9
    -- False on the left can always be used.
    apply False.elim h13
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h14 : ((((p4 ∨ p3) → ((p4 ∨ (p5 ∨ p2)) ∧ False)) ∧ False) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h15
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- False on the left can always be used.
      apply False.elim h17
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h18 := h3 h14
    -- False on the left can always be used.
    apply False.elim h18
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h19 : ((((p4 ∨ p3) → ((p4 ∨ (p5 ∨ p2)) ∧ False)) ∧ False) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h20
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- False on the left can always be used.
      apply False.elim h22
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h23 := h3 h19
    -- False on the left can always be used.
    apply False.elim h23
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h24 := h1 h2
  -- False on the left can always be used.
  apply False.elim h24
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135773511066623122530027185628 : (((((((True ∧ False) ∨ p5) → p2) → (p2 → ((True → p2) ∨ p3))) ∨ p3) → (p4 ∧ ((p5 ∨ True) ∧ (p2 ∧ p5)))) ∨ (True ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650001555199507282622615938635 : ((((((p1 ∨ True) → (p5 ∧ (((p3 → True) ∨ True) → ((True ∨ ((p3 ∨ p4) ∨ p5)) ∧ p2)))) ∨ (p2 ∨ (p3 ∨ p2))) ∧ (p1 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60206457961952843043234444615 : (((True → True) → ((p4 ∨ (((p5 ∧ p2) → ((True ∧ p1) → ((((p4 → False) ∨ True) ∧ p2) ∧ False))) → (p5 ∧ p3))) → (p5 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113726564973655729700891171157 : (((((False → ((p5 ∨ ((p3 ∧ (p5 → (False ∧ p4))) ∧ (p4 → p3))) ∧ p3)) ∧ p2) ∨ (p2 ∧ (p2 ∧ p1))) → (p1 ∧ p5)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185978770953110786743409417059 : (((p5 ∧ ((((p5 ∧ p1) ∨ True) ∨ (p4 → p1)) → False)) ∧ p3) → ((((((p2 → False) → p1) → p4) ∧ p3) ∨ ((p5 → True) → True)) ∧ False)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h11 : (((p5 ∧ p1) ∨ True) ∨ (p4 → p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h12 := h10 h11
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307364680470703961526466841096 : (p1 ∨ (p4 ∨ ((((p5 ∧ p3) ∧ p3) → ((p5 ∨ ((p4 ∧ p1) → p3)) → (((p1 ∨ ((p4 → p4) ∧ False)) → (p3 ∧ p2)) ∨ p2))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67962985953390847576461578192 : ((p2 → (((p3 → True) ∧ p3) ∧ ((True → False) → ((((False ∧ ((((p2 ∧ p5) ∨ p3) ∨ p2) → (p3 ∨ p1))) ∧ p4) ∨ False) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62439317006588009329949745918 : ((p3 ∧ ((p2 ∧ (p1 ∨ p2)) ∧ (False ∧ (p2 ∧ (False → ((p5 ∨ ((((p4 → ((p1 ∧ p5) ∧ p3)) → p3) ∨ p3) → p1)) ∨ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43721725395809447525743838354 : ((((((p2 ∧ p1) ∨ False) → ((p5 → ((p1 ∨ p4) ∧ (((p3 → p5) ∧ ((p2 ∧ (False ∧ False)) ∧ p3)) ∨ False))) ∨ p2)) → p5) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46429180353778311242143192440 : ((((p4 ∧ (p5 → ((False ∧ p2) ∨ p5))) ∨ ((p2 → p5) ∨ ((p2 ∧ p3) ∧ ((p4 → (p1 ∨ p4)) ∧ (p1 → p1))))) ∧ (p2 → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44307438553227292612170340325 : (((((p5 → ((False → ((True → False) ∧ (p2 → p4))) → ((p3 ∨ True) ∧ p3))) ∧ False) ∨ ((True → p1) ∧ ((p4 → p5) ∨ p2))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247503644810749541862703375620 : ((False ∨ p3) ∨ ((p5 ∧ p1) → ((True → (((p5 ∨ p4) ∨ p1) → (p2 ∨ (False ∨ p1)))) ∧ ((((False ∧ True) → False) ∨ (p2 ∨ False)) ∨ p5)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h1.left
      let h10 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h1.left
    let h13 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259814530244364544990687627747 : ((p1 → p3) → ((p4 → ((True ∧ p4) ∧ (((p3 ∨ p1) → (p4 → p3)) → (p2 → ((p2 → False) ∨ p2))))) ∨ (p4 → (p5 ∨ (False → True))))) := by
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
theorem thm_5_vars_350593173754850299014617947640 : (p4 → (((True ∧ (((p5 ∨ False) → p1) ∨ p2)) ∧ ((p1 ∧ (((p3 ∧ True) ∧ True) → p3)) ∧ (((False ∧ p1) ∨ p3) ∨ (False → p1)))) → p1)) := by
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
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h4.left
    let h9 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- False on the left can always be used.
        apply False.elim h14
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h4.left
    let h20 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h19.left
    let h22 := h19.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- False on the left can always be used.
        apply False.elim h25
      case inr h27 =>
        -- One of the premise coincides with the conclusion.
        exact h21
    case inr h28 =>
      -- One of the premise coincides with the conclusion.
      exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699755953307164250258630601089 : (((((((p2 → ((False → True) ∧ p2)) → p4) ∧ p1) ∨ (p3 → p1)) → ((((False → (p3 → p2)) ∧ p4) ∧ (p4 ∨ (False → p5))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205389136398037858461192197486 : ((((False ∧ False) → True) → (p2 ∨ p4)) ∨ ((False → p5) ∨ ((True → False) → (((p5 → (p3 → ((p2 ∧ (p3 ∧ p2)) ∨ p1))) ∧ p3) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312288545373841344853939167889 : (p2 ∨ (p2 → ((((((p1 ∧ ((((p4 ∨ True) ∨ False) → p5) ∧ p2)) → (True ∨ True)) ∧ (p5 → (p3 ∨ p1))) ∨ (False ∨ False)) ∨ p5) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306541021764583645641930673739 : (p1 ∨ ((p4 ∧ p4) → (((p3 ∨ (p5 → p5)) → ((True ∨ (p4 ∨ (((False → (False ∧ p4)) ∧ p3) ∧ ((True ∨ p2) ∨ True)))) ∧ False)) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (p3 ∨ (p5 → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h5
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63102890333449535399874918959 : ((p5 ∧ ((False ∨ ((False ∨ p1) ∨ ((p2 ∨ ((True ∧ False) ∨ (p5 ∧ (p4 → (False → ((p3 → p3) ∨ (True → False))))))) → False))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158732494440871411445018810207 : ((p3 ∧ (p4 ∧ ((((p5 → ((p4 ∨ (p5 ∧ p1)) ∧ ((p3 → False) ∨ p5))) ∨ p4) → p1) → False))) ∨ (p5 ∨ ((p3 ∨ p5) → (True ∨ p2)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720744460056317052619606663201 : (((((p2 ∧ (p5 ∨ p5)) → p4) → (((False ∧ (((True ∨ (p3 → (p1 ∨ p2))) ∨ (((p5 → p3) → p4) ∧ True)) → p3)) ∧ True) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113515023382752371227461318385 : ((((((p2 ∧ p3) → ((p5 ∨ ((p5 ∨ p1) → p4)) → p4)) → p4) → (False ∨ (((p5 → p5) ∧ p2) ∨ p3))) ∨ (p2 ∨ True)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353560402595433456679092446435 : (p4 → (p3 ∨ ((False → ((True ∨ p5) ∨ False)) ∧ ((p2 ∧ ((p1 ∨ ((p5 → p4) ∨ p1)) ∧ (p5 ∨ ((p1 → (True ∨ p3)) ∧ p1)))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227634837327462414338821251654 : ((False ∧ (p3 ∨ p4)) ∨ ((p3 ∨ ((p1 ∧ ((p5 ∨ p5) → p5)) ∨ True)) → (((True → (p1 ∧ (True → True))) ∨ ((p2 → p1) → p3)) ∨ True))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
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
theorem thm_5_vars_119275054412835710359246587611 : ((p3 → (((True ∧ (p1 → (p5 → p2))) ∧ (p2 ∨ (p1 ∧ (((True ∧ ((False → (p4 → p3)) → p5)) ∨ p4) ∨ p1)))) ∧ False)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166128930527346913176258925906 : ((True ∧ ((((p3 → p2) ∨ (p5 → p5)) ∧ (p4 → p1)) → ((False ∨ (False ∧ True)) ∧ False))) ∨ (((False → False) ∧ (p4 → (p1 ∨ p5))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156610368508114542248909694108 : ((((p2 ∧ ((((True → p2) ∧ (False ∨ p2)) ∨ ((False ∨ False) ∧ (p5 ∧ p2))) ∧ p3)) ∧ False) ∧ p1) ∨ (((p5 ∧ p2) → (p3 → p2)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_974358370112392337585436822731 : ((((False → p3) → ((((((p1 → (p4 ∨ (p2 → p5))) → True) → (False → (p5 ∨ (True ∧ p2)))) ∨ False) ∨ (p3 → (p5 ∨ p4))) ∧ False)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622297558336874972027232850646 : ((((p3 ∧ ((((True → True) ∧ (p3 ∧ (p1 ∨ (p4 ∧ (p4 ∨ (((p3 → True) ∧ p5) ∨ p3)))))) → ((p2 ∧ p3) ∧ False)) ∨ True)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_185206768455638048087220832973 : ((True ∧ (False ∧ (False ∧ ((p4 ∧ (p3 → (p2 ∧ True))) → p3)))) ∨ ((p3 ∧ p4) → ((True → p4) ∨ (p3 → (((p2 → False) ∨ p2) ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52263132862247640224520305088 : (((p4 ∨ (p3 ∧ ((((p2 ∨ p2) ∨ p2) → (p2 → p1)) ∨ ((False ∨ False) → p2)))) → (False ∨ (((p1 ∨ True) ∨ p3) ∨ (p4 ∧ True)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14945022509264589606314050503 : (((((p2 → p3) ∧ p2) ∨ (p2 ∨ (False ∨ ((True ∧ (p1 → (p5 ∨ p2))) ∧ ((p5 → (p1 → True)) → (p2 ∧ p4)))))) ∨ (False → p1)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352092072834928758432672775275 : (p4 → ((((True ∧ p1) → (p5 ∨ p3)) ∧ p3) ∨ (p4 → (((p5 → ((((True → p4) → (False → p5)) → p3) ∨ p5)) ∧ p4) ∧ (p4 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116719627165962038711258459427 : (((p2 ∧ p2) ∨ (p5 ∨ ((p4 → p5) → ((((True ∧ ((p3 ∨ p5) → p4)) ∨ (p5 ∧ p1)) → p5) ∨ ((p2 ∨ p5) ∨ False))))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41094190473995782835786438196 : ((((((p2 → p1) ∨ (((p2 → p2) ∧ (p3 ∧ (p1 ∨ (False → p3)))) → (p2 → p4))) ∨ (p2 ∨ False)) ∧ (p4 ∧ (False ∨ p4))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186346347771734573778925072492 : (((((False ∨ p1) ∧ p4) ∨ (p4 → ((False ∧ p1) → p2))) → p3) → (((p1 ∧ ((p1 ∧ (p5 → p5)) ∧ (p5 ∨ (False → p5)))) ∧ p2) → p2)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h11 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55711194112429716688832306911 : ((((True → (p2 → p4)) ∨ p1) ∧ (((((p2 → (False ∨ (p1 ∨ p4))) ∧ False) → (True → p4)) → p4) ∨ ((p2 ∨ (p3 ∧ False)) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48294223526236727870032544713 : (((p5 ∧ (((p1 ∧ p3) → p5) ∧ (((p5 ∨ p2) ∧ (p5 → True)) ∧ (((p2 ∨ p4) ∧ ((p2 ∨ p4) → True)) ∧ p2)))) → (p1 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51959032530670527293584431065 : ((((p3 ∨ ((p3 ∨ p2) ∧ p2)) ∨ (((p2 ∨ p4) ∨ p1) ∧ (p5 ∨ (p2 → p5)))) ∨ ((p2 ∨ (True ∨ ((False ∨ True) → p5))) ∧ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720482064097732319668684424291 : (((((p1 ∨ (p3 ∨ p4)) ∨ p1) → ((p3 ∨ (((p4 ∧ (True ∧ False)) ∨ (p5 ∧ True)) → True)) ∧ ((p4 ∧ p5) ∨ (p4 ∨ (p2 → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147322793632545180569923578010 : ((((((p4 → p1) ∧ (False ∨ (p2 → (p5 → (False ∨ ((p3 ∨ p3) ∧ True)))))) ∨ p3) ∧ (p2 → False)) ∨ True) ∨ (((p3 → True) → p3) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204698878055670913322966471893 : (((p3 ∨ (p1 → (p3 ∧ p4))) ∨ p1) ∨ ((False ∧ ((p2 → (((p5 ∧ p2) → True) → ((True ∨ (p1 → p1)) → (p4 ∧ p5)))) → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207149992066024439217028741168 : (((p1 → (False → (False ∧ p4))) ∧ True) → ((((p3 → p5) → p1) ∧ ((p5 ∨ (((((False → True) ∧ p4) ∧ p1) → p4) → p2)) ∧ p5)) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_431727773184236239668441194634 : ((((p5 ∧ (p2 ∨ ((((p4 ∨ p1) → ((p5 ∧ (p4 ∨ True)) → False)) ∨ (p5 → p3)) ∧ (((True ∧ True) ∨ p5) → p4)))) ∨ (p2 → p2)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723833893494090195325949507725 : (((((p4 → p4) → p4) ∧ ((p3 → (False ∨ (p3 → (((p4 ∧ p4) → p4) ∨ ((((p2 ∨ p5) ∧ p4) ∨ False) ∨ p5))))) ∧ (p1 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111894912877523780351441728806 : ((((((p4 → (p1 ∧ p1)) → False) ∧ ((p4 ∨ (p3 ∨ p4)) ∧ (p5 ∧ p2))) ∨ (False → ((True ∨ p1) ∨ (p5 ∨ p3)))) ∨ p4) ∨ (p2 ∨ p3)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346907492511910085794159175992 : (p3 → ((((p2 → (p3 → (p3 ∨ ((True ∧ p4) ∧ True)))) ∨ (True → p3)) → ((True → p1) ∨ p4)) ∨ ((False ∧ (p2 ∨ p3)) → (p1 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42958688475869296585662603219 : (((p5 → (((p4 ∧ (((p4 → (p4 → p2)) ∧ True) → (((p2 → (p5 ∨ p1)) ∨ (p4 → (p1 ∨ p3))) ∧ p1))) ∨ p5) ∧ p5)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253014033714077576568478069635 : ((True ∧ p3) → ((((True → ((((True ∧ p3) ∧ (p1 ∧ True)) ∧ (p2 ∧ p2)) → p4)) → p1) ∨ p3) ∨ ((((p4 ∧ p5) ∨ p3) ∧ p1) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47444662464913410389710434382 : (((p3 ∧ (((((p4 ∧ p1) → False) → p5) ∧ (p5 ∧ p2)) ∨ ((((p5 ∨ p5) ∨ p2) ∧ p3) ∧ (p5 ∨ (p2 ∧ True))))) ∨ (False ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37051010436710281997469277115 : (((((((((p3 ∨ (p4 ∧ p2)) ∧ (((((p1 ∨ False) → p5) ∨ p3) → p5) ∨ (p5 ∨ True))) ∧ p3) ∨ p1) → p4) ∧ p3) ∧ p5) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113857999761995439612174587564 : (((p2 → ((((True ∧ False) → p5) ∨ (p2 ∨ ((True ∨ (False → p4)) ∧ (p5 → (p3 ∧ (p1 ∧ True)))))) ∨ p4)) → (False ∧ p2)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350252106566804624400882850991 : (p4 → ((False ∧ (p2 ∨ (((p3 ∧ (((((p2 → p4) → False) ∨ p2) → False) → (p4 ∧ (p1 ∨ True)))) → False) ∨ ((True → p3) → p3)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105577822832843497038729606156 : (((((p4 → p1) ∨ True) ∨ (False ∨ (((p4 ∧ p5) → p3) → (((p3 → p2) → False) ∧ p1)))) → ((p3 ∧ (p5 → False)) ∨ True)) ∧ (p5 → p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Implications on the right can always be decomposed.
  intro h8
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213410320647792288659776657199 : (((p2 ∨ (False ∧ p5)) ∧ p3) ∨ (((False → (False ∨ p2)) → (p4 ∧ ((True → (p2 ∨ p4)) ∨ (True → False)))) ∨ (True ∨ ((True → p3) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198404515278682886888228843080 : ((p4 ∧ ((p1 ∧ (p3 ∧ (p4 ∨ p1))) ∧ p1)) ∨ ((((True → True) ∧ (p4 ∧ p4)) → (p3 → (p4 ∨ (False ∨ (p4 ∨ p1))))) ∧ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157862476054222353854981973051 : (((p4 ∨ ((p3 ∧ (p3 ∨ (p3 ∨ (p3 ∧ False)))) → p4)) ∧ ((((p3 ∨ p4) → p2) → p2) → p2)) ∨ (p4 ∨ (p3 ∨ (p2 → (True ∨ p3))))) := by
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
theorem thm_5_vars_197052111598089027365381628729 : ((((p2 ∧ p4) ∨ (True → (p2 ∨ p1))) ∨ p2) ∨ (False → ((p3 ∨ (p1 ∧ p3)) ∨ ((p3 ∨ (True ∧ (p4 ∨ p5))) → ((True ∧ True) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41950129767328215355665364181 : ((((p1 ∧ p5) ∧ (((((True ∨ (p2 ∧ p3)) ∨ (True ∨ p5)) ∨ p1) ∧ p4) ∧ (p1 ∧ ((((p2 → p4) ∧ p2) → False) ∨ False)))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48693904540820707433213896192 : (((((p4 ∧ (False ∧ ((p4 ∨ True) ∨ p3))) → p4) → (True → ((p2 ∧ False) ∨ (p3 → ((p1 ∨ p5) → p2))))) ∧ (True ∧ (p4 → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783664105295934581827447281516 : (((p3 ∨ (((True ∨ (False ∧ p5)) → (True → (False ∧ p1))) → ((p3 ∨ p3) ∧ ((p2 ∧ ((False ∨ p4) ∧ p2)) ∧ ((p2 ∧ False) ∨ True))))) ∨ False) ∧ True) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (False ∧ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (True ∨ (False ∧ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h12 : (True ∨ (False ∧ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h12
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h14 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h15 := h13 h14
  -- We need to get the left conjuct of h15 based on <expert-advice>.
  let h16 := h15.left
  -- False on the left can always be used.
  apply False.elim h16
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h17 : (True ∨ (False ∧ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h18 := h1 h17
  -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
  have h19 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h18, we can now drive its conclusion.
  let h20 := h18 h19
  -- We need to get the left conjuct of h20 based on <expert-advice>.
  let h21 := h20.left
  -- False on the left can always be used.
  apply False.elim h21
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736054297684469414234284039871 : ((((True → p4) ∧ (p5 ∨ (((False ∧ (p1 → p3)) ∧ (p2 ∨ (((False ∨ (p4 → p2)) ∨ (p4 ∧ (p4 ∨ p3))) ∨ (False ∧ p2)))) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624627501383155059658304245271 : ((((p4 ∨ (((False ∨ (p1 ∨ True)) ∨ p4) → ((((True → p2) ∨ False) ∧ (False → (p1 ∧ (True ∧ (p5 ∧ (True ∧ False)))))) ∧ p1))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_57822591758115315574417657943 : (((p3 ∧ (p3 → p3)) → ((p4 → (p1 ∨ (((((True → (p2 → p5)) → ((p3 ∨ False) ∧ False)) ∧ p2) → (p3 ∧ p4)) → p1))) ∨ p3)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_84142847630988856696736528525 : (((p3 ∧ (((False ∧ (p3 ∨ (((True ∧ p1) ∧ (p1 → p1)) → False))) ∨ p3) → False)) ∧ ((False ∧ (p5 ∧ p5)) → (True ∨ (p2 ∧ p4)))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((False ∧ (p3 ∨ (((True ∧ p1) ∧ (p1 → p1)) → False))) ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198386450458208713931435178326 : ((p3 ∧ ((p5 → p2) ∨ ((p3 ∨ p4) ∨ False))) ∨ ((p2 → True) → (p5 → (p1 ∨ (((p3 → ((p1 → (False ∨ p5)) ∨ p1)) ∨ p2) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708902720694543035283345846102 : (((((((p5 → p2) ∧ p5) → p2) ∨ (p3 → True)) → ((p1 ∨ p3) ∨ ((False ∧ (p5 ∨ False)) ∧ (p5 → ((p3 ∨ p3) ∨ (p4 ∨ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245285816800792978264424743001 : ((p2 ∧ p2) ∨ ((p5 → (((((p1 → p4) → False) ∧ ((((True → p1) → p4) ∨ p5) → False)) ∧ p5) ∨ (p5 ∨ (False ∧ (False ∧ p5))))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8353879009613851606332246905 : ((((((p2 → p2) → ((p5 ∧ (True ∨ True)) ∨ p5)) ∧ (p4 → ((p4 ∨ (False → p4)) ∧ (((p2 → p4) ∧ p5) ∧ p1)))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790936161303156662537331239274 : (((p5 ∨ (p4 → (p3 ∧ (True → (((((p4 → p3) ∧ ((p1 ∨ (p5 → ((False ∧ p5) ∧ p3))) ∨ p3)) ∨ p4) ∧ (p3 → p4)) → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57005376056425756635994255777 : (((True → (False → p2)) ∧ ((p2 ∨ ((((p4 → (p3 ∧ p4)) → True) ∧ p5) ∧ ((((False → True) → p5) ∨ True) ∨ False))) ∨ (p2 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709628871162232830044075977886 : ((((p2 ∨ (p5 → ((p5 ∧ (False → p5)) ∧ p4))) → (((p2 → (p1 → (((((p2 → p4) ∧ False) → p3) ∧ p1) → p2))) ∨ p3) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675364721932489461319431162689 : (((((((True ∨ p5) → ((p5 ∧ (p2 ∧ ((p3 ∧ (p1 → p5)) ∧ p2))) ∨ p2)) ∨ (p1 → False)) → p5) ∧ ((p5 ∨ (p4 → p4)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209591391504423640908616066281 : ((p5 → (False → (p2 → (False ∧ p3)))) → ((((p3 → ((p3 → False) ∧ p2)) ∧ p1) ∨ p3) ∨ (False → ((True → ((True → p5) ∨ p3)) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171844865535979572747867779889 : ((((False → p5) ∧ ((p4 → ((p2 ∧ ((p5 ∨ p4) → p3)) → False)) → p3)) → p1) ∨ (((True → (True ∨ (False ∧ p3))) ∨ p4) ∨ (p4 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259200773792008523542937406043 : ((False → False) → (((p4 ∨ (True ∧ (((True → p5) → p2) ∧ ((((p4 → True) → p2) ∨ p1) → True)))) ∨ ((p2 → False) ∨ True)) ∨ (False → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300391838845517215796040789990 : (False ∨ ((((p2 ∨ p2) ∧ True) ∨ ((((p4 ∧ p2) ∧ False) ∨ ((True → (((False ∨ p5) ∧ p5) ∧ False)) → p5)) ∧ True)) ∨ (p1 ∨ (p3 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179215373006264784213633271269 : ((p4 ∧ (((True ∧ (((p1 ∨ p2) ∧ p2) → True)) ∨ p1) → (False ∧ True))) ∨ (p4 → ((p5 → (True → (((p5 → p5) ∧ p5) → False))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62873835322048351277030685954 : ((p4 ∧ (((p3 ∨ p3) ∧ p5) → ((p1 → (p3 → (((p5 → p4) ∨ p2) → p5))) → ((p2 ∧ (False → p2)) ∧ (False → (p3 → p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66120645760560216896984852015 : ((p5 ∨ ((p5 ∨ ((p1 ∨ p2) → ((p1 ∧ p2) ∧ ((((p4 ∧ (p1 ∨ p3)) ∨ (p2 ∧ (p3 ∧ p1))) → (p4 ∨ True)) → p4)))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244995093615949614905622550700 : ((p1 ∧ p4) ∨ ((p1 ∨ (p5 ∨ (False ∨ (p3 ∧ (((False → (p1 ∨ p2)) ∧ (p5 → ((p3 ∨ p3) → p4))) ∨ p4))))) → (False ∨ (p4 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h15
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h17
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_72135826552838294266712622479 : (((True → (True ∧ ((((((p5 ∨ p4) → p3) ∨ (p4 ∨ p1)) → (((p1 → p4) → (p3 ∧ (p2 ∧ True))) → False)) → p5) ∧ p2))) ∧ True) → p2) := by
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
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114856106944442352394102893450 : ((((p5 ∨ ((p2 ∨ (((p4 ∨ False) → p4) → p2)) → (p4 ∧ p2))) → False) ∨ ((True ∧ p4) → (True ∨ ((p3 ∨ p3) ∧ p5)))) ∨ (False ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_62170631932063614828058453480 : ((p2 ∧ (p4 → ((p3 ∧ ((((False ∨ p1) ∨ True) ∨ (p3 ∨ False)) → (p5 ∧ ((True ∨ (((False → p2) → p3) ∧ p4)) → True)))) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190968853391689440462204306350 : (((((p3 ∧ p2) ∧ p4) ∧ p1) ∨ (True → (p4 ∧ p2))) ∨ (((p5 ∧ ((p2 ∨ p2) ∧ (p5 ∧ p2))) → (p2 ∨ (p3 → p5))) → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46195961272483102916495713963 : ((((p4 ∨ ((p4 ∨ False) ∧ (p5 → (((p1 → True) → ((False ∨ p5) → p5)) ∧ (p1 ∧ (p2 ∨ (True ∧ False))))))) → p2) ∧ (False ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142025789026317887650370554830 : (((p3 → p3) → ((True ∨ ((p3 ∨ False) → ((p1 ∨ False) ∨ p4))) → (p4 ∧ (((p5 ∧ False) ∧ p5) ∧ (p4 → p3))))) → (p3 ∧ (p1 → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (True ∨ ((p3 ∨ False) → ((p1 ∨ False) ∨ p4))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h12 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h13
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h14 := h1 h12
  -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
  have h15 : (True ∨ ((p3 ∨ False) → ((p1 ∨ False) ∨ p4))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h14, we can now drive its conclusion.
  let h16 := h14 h15
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- We need to get the left conjuct of h17 based on <expert-advice>.
  let h18 := h17.left
  -- We need to get the left conjuct of h18 based on <expert-advice>.
  let h19 := h18.left
  -- We need to get the right conjuct of h19 based on <expert-advice>.
  let h20 := h19.right
  -- False on the left can always be used.
  apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184166810285849274854408726768 : (((True → ((p5 ∨ ((p4 ∧ False) ∧ False)) ∧ (p1 ∧ p3))) ∨ p1) ∨ (((((True ∧ p2) → p5) → p2) ∨ True) ∨ ((p4 ∧ p5) → (p2 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354612292463149596728980574902 : (p5 → ((((p4 ∨ (((False ∨ (((p4 → True) ∨ p4) ∧ p3)) ∧ (((False → True) ∨ True) → p1)) ∧ False)) ∨ (p1 → (p3 ∧ True))) ∨ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46334229738468759037659556561 : ((((p4 → ((((p4 ∨ False) ∨ (p5 ∨ (True ∨ (p5 ∨ (False ∧ True))))) ∨ p3) ∨ p5)) → (p1 ∧ (p1 ∧ (True → p1)))) ∧ (p4 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722119145915827142485991897167 : ((((p3 → ((p2 → True) ∧ p5)) → (((True ∨ ((True ∨ ((p1 → p1) ∧ (p4 ∨ ((p1 ∨ p2) ∧ (p3 → p3))))) ∨ True)) ∨ True) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



