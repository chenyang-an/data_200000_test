variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774469297097086804906495743290 : (((False ∨ (((p2 ∨ ((p4 ∨ True) ∨ (p5 → (((p2 → p3) ∧ p4) ∧ (p2 ∧ False))))) → False) → (((p1 ∨ (p5 ∧ p5)) ∨ p3) → p4))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h5 : (p2 ∨ ((p4 ∨ True) ∨ (p5 → (((p2 → p3) ∧ p4) ∧ (p2 ∧ False))))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h6 := h1 h5
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h10 : (p2 ∨ ((p4 ∨ True) ∨ (p5 → (((p2 → p3) ∧ p4) ∧ (p2 ∧ False))))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h11 := h1 h10
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h13 : (p2 ∨ ((p4 ∨ True) ∨ (p5 → (((p2 → p3) ∧ p4) ∧ (p2 ∧ False))))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h14 := h1 h13
    -- False on the left can always be used.
    apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184751683013089262561729996455 : ((((False ∨ False) ∨ (p1 → p2)) ∧ (((p3 → False) ∨ False) ∧ p3)) ∨ (True ∨ (((p4 ∧ p4) ∨ ((((True ∧ False) → p2) ∨ p5) ∧ p5)) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56233481011066090184725136767 : (((p4 ∨ (p5 ∨ (p4 ∧ p4))) ∨ (((((p2 → (((False ∨ p3) → True) ∨ p4)) ∨ p1) ∧ True) → ((True ∧ p5) ∧ p1)) ∨ (p3 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49468249619949170542405947719 : ((((((p3 ∨ ((p4 ∨ p5) → p3)) ∧ ((False ∨ ((False ∧ p4) ∨ ((True → p5) → p2))) ∨ False)) ∧ p5) → True) → ((p3 → p1) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45989923528747797018664284901 : (((((((p1 ∨ True) ∧ (False → (((p2 → p1) ∧ (True ∨ ((p3 ∧ p3) ∧ False))) ∧ False))) ∧ (p5 → p3)) → p1) ∧ p5) ∧ (p2 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684267052313283239637293266887 : (((((p2 ∨ ((p3 ∨ (p4 ∨ p3)) ∨ (p1 → (p1 → (p5 ∧ True))))) ∧ (False ∧ (False ∨ p3))) ∨ (((p5 ∨ (p1 → p5)) → p1) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342018665487653842760538705754 : (p2 → ((p5 ∨ ((True → (True ∨ (p4 ∧ p5))) → (((((p4 ∨ True) ∧ False) ∧ p5) → p3) → (p5 → (False ∧ False))))) ∨ ((False ∨ True) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135361962028082851225864644755 : (((p2 → ((((False ∧ (p4 ∨ (((p3 ∧ p3) ∧ False) ∧ p4))) ∧ (True ∧ False)) → p3) → p5)) ∧ (p4 ∧ (p4 → False))) ∨ (True ∨ (p5 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196425137597547600847971284338 : ((False → ((((p4 ∧ False) ∧ p5) ∧ p3) ∨ p5)) ∧ ((((p2 → ((p1 ∧ False) ∧ p5)) → (False ∨ (p5 ∧ p1))) → p3) ∨ ((False ∧ p1) → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
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
theorem thm_5_vars_67770009899136987044785696111 : ((p2 → (((p4 ∧ (p5 → False)) ∧ (((p3 ∨ p2) ∧ ((p2 → False) ∨ (False ∧ (p3 → p5)))) ∨ (p4 → ((True → False) ∧ True)))) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111334059620708209667617684116 : (((p2 ∧ (True → ((((p3 ∨ False) ∧ ((False ∧ (((True ∨ p4) ∧ p4) ∨ p1)) ∧ ((p1 → p2) ∧ False))) ∧ p3) ∨ p4))) ∧ True) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117113592832606816807864745085 : (((p3 → p1) → ((((p1 → (True ∧ (p5 ∨ p4))) ∨ ((p4 ∨ (((p5 ∨ p2) ∧ False) ∨ p2)) ∧ False)) ∧ (p2 ∧ p1)) ∨ p5)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246131269949134439799792098790 : ((p4 ∧ p2) ∨ ((((((True ∨ p2) ∨ p3) ∨ True) ∧ (((((p4 ∨ (p5 → p5)) → False) ∨ (False → p4)) → p2) ∨ (True → p1))) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711869617524830366066550932357 : (((((p5 ∧ ((True ∧ p2) ∨ p1)) ∧ p2) ∨ (p3 → ((((p2 ∨ (p2 → (p1 ∧ p2))) ∧ True) ∨ (True ∧ p4)) ∨ ((p1 → p3) ∨ p4)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46966329664774884259003851425 : ((((((p4 → p4) ∨ (p2 ∨ (False → (p1 ∨ ((p4 ∧ p2) → (True → ((p5 ∨ p1) ∧ (p1 → True)))))))) ∨ True) → p5) ∨ (p3 → True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119463233822361981103367462360 : ((p4 → ((p3 ∧ False) ∧ (((((p4 ∨ False) → (p4 ∨ (p2 ∨ (p2 → ((p1 ∧ p2) ∧ p3))))) ∧ True) ∧ (p5 ∨ p5)) ∨ False))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55415402705051777693735984169 : (((((p1 ∨ p5) ∨ (False → p2)) ∨ p5) → ((True → ((((p4 ∨ p1) ∨ True) → (True ∧ p3)) → ((False ∧ p4) ∨ p3))) ∧ (p1 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658265050811084029748450674631 : ((((p5 ∧ (p3 → ((p2 → (p4 ∨ (p5 → (p4 ∧ (p4 ∨ ((((p3 → p2) ∨ p4) ∨ (p2 → p3)) ∨ p4)))))) ∧ p4))) ∨ (p4 → True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_148444800783183018084531122607 : ((((((((p4 ∨ True) → p1) → False) ∧ (p4 ∨ p3)) → p3) ∧ p4) ∧ (p1 → ((p2 → (p2 ∨ p3)) → False))) ∨ (((p4 ∧ p3) → p4) ∨ p2)) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59948326630355919407753182300 : (((True ∨ p2) → (((p3 ∨ (p4 ∨ (p5 ∨ True))) ∧ (True → ((False ∨ (p3 ∧ False)) → p1))) ∨ ((p4 → (p3 → (p1 ∧ False))) → p3))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340927638358624676798161395533 : (p2 → ((((p3 ∨ (False → (p1 → False))) ∨ False) → ((p3 ∨ (((p2 ∨ p3) ∧ (p1 → (p5 ∨ p3))) ∧ ((False ∨ p1) ∨ p1))) → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260924989063818505592970133232 : ((p4 → False) → ((True ∨ p2) → (((((((p1 ∧ p2) ∨ p5) → ((p1 ∨ p3) ∨ p3)) ∨ True) ∧ p4) → ((p2 ∧ p1) ∨ p1)) ∨ (p3 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h8 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h9 := h1 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h11 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h12 := h1 h11
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h17 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h18 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h19 := h1 h18
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h21 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h22 := h1 h21
      -- False on the left can always be used.
      apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67636678116388252012464471638 : ((p1 → (False ∨ ((p4 ∧ (p5 ∧ ((p5 → (p3 ∧ p5)) ∨ p5))) ∨ (((p2 ∨ ((((p3 ∧ p1) ∨ p1) ∧ p4) → p2)) ∧ p2) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55184447653082709181811159366 : (((((p4 ∧ False) ∨ (False → p5)) → p5) ∨ (p2 → (((p1 ∧ (False ∨ p3)) ∧ p3) → (((p5 ∨ False) ∨ (True ∨ (p2 ∨ p3))) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228958932728554172560308264139 : ((p4 ∨ (p1 → False)) ∨ (p1 ∨ ((True → p5) ∨ ((((False ∧ p5) ∨ (p2 ∨ (False → p5))) ∨ (p2 → ((p5 → (p2 → p2)) ∧ p1))) ∨ p4)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316883338166524062119014855748 : (p3 ∨ (p1 → ((p3 ∧ (True → False)) → ((((p3 ∧ (p1 ∨ (p1 ∧ False))) ∧ p2) ∨ (((p4 ∨ (p3 → p4)) ∨ p3) ∨ p4)) ∧ (p4 ∨ False))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136774104907064301270837584287 : (((p5 ∨ p4) ∧ ((((p1 ∨ (((p5 ∧ False) ∨ p4) ∨ ((p1 ∨ (p4 → True)) ∧ False))) ∧ p4) ∨ p2) ∧ (p4 ∨ False))) ∨ ((p4 ∧ p1) → p1)) := by
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
theorem thm_5_vars_756368107090267026986834343448 : (((p1 ∧ ((p5 ∧ (p1 ∧ (((p5 ∨ p1) → ((False → (p1 → (False → (p4 ∧ p3)))) ∨ p1)) ∧ (p4 ∨ p4)))) ∧ ((p2 ∨ p3) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141298380797718860299940543528 : (((p3 ∧ ((True ∧ p1) → p4)) ∧ (p1 ∧ (((p5 → p5) ∧ ((p3 ∨ ((p5 ∨ (p4 ∨ False)) → p5)) ∧ p3)) ∨ p4))) → ((p5 ∨ p3) ∧ p4)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h17.left
  let h21 := h17.right
  -- Disjunctions on the left can always be decomposed.
  cases h21
  case inl h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h27 =>
      -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
      have h28 : (True ∧ p1) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h20
      -- We have shown the premise of h19, we can now drive its conclusion.
      let h29 := h19 h28
      -- One of the premise coincides with the conclusion.
      exact h29
    case inr h30 =>
      -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
      have h31 : (True ∧ p1) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h20
      -- We have shown the premise of h19, we can now drive its conclusion.
      let h32 := h19 h31
      -- One of the premise coincides with the conclusion.
      exact h32
  case inr h33 =>
    -- One of the premise coincides with the conclusion.
    exact h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707859317514055465084939432988 : ((((p2 ∧ (True → ((p2 → p5) → (p3 ∨ p3)))) ∨ ((False ∨ ((True ∨ False) → (p3 ∨ (p2 ∨ (((True ∨ p2) → p3) → True))))) ∧ True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250818079965977901897303304458 : ((p1 → p2) ∨ ((((((True ∨ (p5 ∨ p4)) → (((p5 → False) ∨ (False ∨ True)) ∧ (True → p1))) ∨ True) ∨ (p5 → p2)) ∨ p3) ∧ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165689248065950523983680832465 : ((((True ∧ False) → ((False → p5) ∧ p4)) → ((p2 ∨ False) → (((True → True) → p3) ∧ p3))) ∨ ((True → True) ∧ (p5 → (True ∨ (False ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48998728032841256613062777355 : ((((p5 ∨ ((p3 → p5) ∧ ((p4 ∧ ((True → p1) ∧ ((p3 ∨ (p2 → True)) → (False ∨ p1)))) ∧ p1))) ∨ True) ∨ (p5 ∧ (p2 → p3))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37274951307540358086527781978 : ((((False ∨ ((((False ∧ ((p1 → (True → ((p5 → True) → p3))) ∧ ((p3 → p5) ∨ False))) ∧ True) → p5) → (p3 ∧ p4))) ∧ p5) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321036754630926837284232327985 : (p4 ∨ (False ∨ (p5 ∨ (p2 ∨ (False ∨ (False → (((True ∨ p3) ∨ p4) ∧ (p3 ∨ (((p4 ∧ p5) ∨ ((p5 ∨ (p3 ∨ p2)) → p3)) ∧ p2))))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757553826268313458672423782339 : (((p1 ∧ (p2 ∧ (((p4 ∧ (p5 → False)) → ((((False → (p4 → (p2 ∨ True))) ∨ p3) ∨ (False → p3)) → (False ∧ True))) ∧ (p5 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356386968093088456191500180536 : (p5 → ((((p4 → True) → p2) ∧ ((((p5 → (False → p1)) ∨ p5) ∧ True) → True)) → ((p3 ∨ p4) ∨ (p4 ∨ (((p4 ∧ p2) → False) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803773195397280936811625424608 : (((p3 → ((p3 ∧ (((((p2 ∧ p2) ∧ ((False → True) → ((p3 ∨ p1) → (p3 ∨ p3)))) ∧ (p5 → True)) ∨ False) ∨ p5)) ∧ (False ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135409080099437030832545881024 : (((((True ∨ p4) ∨ p2) ∧ (p4 ∨ ((p1 ∨ ((False ∧ ((p3 → False) ∧ p3)) ∨ p2)) ∧ True))) ∨ (False → (False ∧ p1))) ∨ (False ∨ (False ∧ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_69051693671567378208701723890 : ((p5 → ((p2 ∧ (((p2 → ((True → p5) → (True ∨ p3))) ∧ p3) → (((True ∨ p4) → ((p5 ∨ True) ∧ True)) → (p1 ∧ p2)))) ∨ p5)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198242642391329837198651472090 : ((True ∧ (p5 ∧ ((False ∨ (False ∨ p5)) ∧ p1))) ∨ (((((p2 ∧ p2) → p1) → (p5 ∨ (p4 ∧ p5))) ∧ (p1 ∧ True)) → ((p2 ∨ True) ∨ False))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690324096917152656672644058989 : ((((p2 → ((p2 → False) ∨ (False ∧ (((((p2 → p4) → p3) → p1) ∧ p5) ∧ True)))) ∨ ((False ∨ (p4 ∨ (False ∧ (True ∨ p2)))) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_149359915403024973700006377855 : (((p5 ∨ p5) → (((p4 ∨ (p5 → ((p1 → (p3 ∨ (p2 ∧ p5))) ∧ p4))) ∧ p1) → (p4 ∧ (p3 ∨ p1)))) ∨ (p4 ∧ ((p4 → True) ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h10 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h11 := h8 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h14 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h15 := h8 h14
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- One of the premise coincides with the conclusion.
      exact h16
  -- Conjunctions on the left can always be decomposed.
  let h17 := h2.left
  let h18 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51850993689366772972982068275 : ((((False ∧ ((p2 ∧ ((p3 → p3) ∨ p4)) ∨ ((False → (p5 ∧ True)) → False))) ∧ True) ∨ (((False ∧ ((True ∨ p4) ∧ p4)) → p1) ∨ p1)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345601565221772454238686620540 : (p3 → (((p1 ∨ p2) ∨ ((p5 ∧ p5) ∨ ((False ∧ ((p2 → ((p5 ∨ p5) ∧ (p1 ∧ p1))) → p1)) ∨ (True ∧ ((p4 → False) ∧ p3))))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207387172411354280474409127036 : (((p1 ∧ ((p4 ∨ p3) → True)) ∨ p3) → ((((((((p2 → p2) ∧ p3) ∨ p5) → p4) ∧ p3) → p4) → p5) ∨ ((p4 → p2) → (p1 ∨ True)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324277559830301159442865166788 : (p5 ∨ ((p5 ∨ ((p5 ∧ (p5 ∧ (p2 ∧ p3))) ∨ p3)) ∨ ((False ∧ p4) → ((True → False) ∨ (((p2 → ((True ∧ False) ∧ p4)) ∨ True) → True))))) := by
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
theorem thm_5_vars_135138086103913176983971276164 : (((False ∨ ((((False ∨ (False ∧ p2)) → False) → p5) → ((True → p4) ∨ (p1 ∧ ((p1 ∨ p1) ∨ p2))))) ∨ (p1 ∨ p2)) ∨ (p1 ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300867842742445549934757551384 : (False ∨ ((((p2 ∨ (((p2 → (p5 ∨ p1)) ∨ p3) → p1)) → (p1 → p2)) ∨ p1) ∨ ((p3 ∨ (True ∨ p1)) ∧ (False → ((p2 ∧ p3) ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172442294517326717274765990484 : (((((False ∧ p2) ∨ p4) ∨ p5) ∨ (p4 → (p3 ∨ ((False → p2) ∧ (False → p3))))) ∨ (p4 ∨ ((((p4 ∧ False) ∨ True) → p2) ∧ (p2 → False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190552997560669386766402618875 : ((((p1 → ((False ∨ p5) ∧ False)) ∨ (p1 ∨ p4)) → p1) ∨ (((p3 → p1) ∧ p1) → (((p5 ∨ p3) ∧ (p2 ∧ (p1 → False))) → (p3 ∧ p3)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h10 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h11 := h7 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h4.left
    let h14 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h1.left
    let h16 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h12
  -- Conjunctions on the left can always be decomposed.
  let h17 := h2.left
  let h18 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h18.left
    let h21 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h1.left
    let h23 := h1.right
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h24 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h23
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h25 := h21 h24
    -- False on the left can always be used.
    apply False.elim h25
  case inr h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h18.left
    let h28 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h29 := h1.left
    let h30 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103185213047236751537000547842 : ((((p1 → True) → ((True → (((p2 → p5) ∨ (p1 → (p3 ∧ p2))) ∨ p2)) → ((p3 ∧ (p1 ∧ p3)) ∨ (p5 → p3)))) ∨ True) ∧ (True ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219653296821880364971565311351 : ((False → (p2 ∧ (p1 → False))) → (((p4 ∨ ((p1 → p3) ∧ (False → ((False → p2) → (p4 → ((p1 ∧ True) ∨ p3)))))) ∧ (p5 ∨ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199458745592478440959470811644 : (((p5 ∧ ((p5 ∨ p3) → (p1 → False))) ∨ False) → ((p2 → ((p2 ∧ (p5 → (True ∧ (((False → p2) ∨ (False → p1)) → p1)))) ∨ p3)) ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258146217332018616724443635112 : ((p4 ∨ p3) → (p2 → (((False ∨ p2) ∧ (False ∨ (p5 → ((p1 ∧ ((True ∨ (((p1 → p1) ∨ p1) ∧ p5)) ∧ p4)) ∧ (True → p2))))) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320432100798680566295311333059 : (p4 ∨ ((p1 ∨ p3) → (((p3 ∧ (p1 ∨ (True ∧ False))) ∧ True) → (((p3 → False) ∧ (False ∧ False)) ∨ ((((p3 ∨ True) ∨ False) ∧ False) ∨ p3))))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187048713086361900529527549652 : (((p3 ∧ p5) ∧ (p3 → (((False ∨ p3) → (p5 → True)) ∧ p5))) → ((p4 ∧ p3) ∨ ((((p5 → (False ∨ (False ∨ True))) → p4) → p1) ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111686485235694532056874570438 : ((((((p4 → (p2 ∨ ((False → (p4 ∧ p5)) → ((True → p5) → ((p2 ∧ p3) ∧ p2))))) ∨ (False ∧ p3)) ∨ p5) → p4) ∨ p2) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250937810465205042843608766967 : ((p1 → p4) ∨ ((True ∧ (((((False → p3) → p1) ∨ True) ∨ p5) → (((True ∧ True) → p4) ∨ (p4 ∧ ((p1 ∨ True) → (p1 → True)))))) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((False → p3) → p1) ∨ True) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (True ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147375430705948875247480713595 : ((((True ∨ ((p3 → (p4 ∨ (p2 → (p5 ∧ (p2 ∨ p3))))) ∧ p3)) → (p2 → ((p2 ∧ p1) ∧ False))) ∨ True) ∨ (p2 ∧ (p2 → (p2 ∧ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635966656650517404638399573313 : (((((((True ∧ (p3 → p3)) → (((((p5 ∧ True) → p3) ∨ p4) ∧ False) ∨ p1)) → True) ∧ (p4 ∧ (p1 ∨ ((False → p4) → p2)))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_431854390197436694745630366336 : ((((False ∨ ((p4 ∨ (((p1 ∨ p5) ∧ (False → p1)) ∧ (p4 ∨ True))) → (p4 → ((p5 ∧ False) ∨ (True ∨ (p1 ∨ p5)))))) ∨ (p3 ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_282501411352906403944008786 : (((True ∨ (p4 ∨ (((p5 → (False ∧ p1)) ∧ p4) ∧ True))) → (((p5 ∧ p3) ∨ True) ∨ (((True ∧ False) ∧ p2) ∧ (p4 ∧ p5)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38385059798738138624193820590 : ((((((p5 ∧ (p3 → p4)) ∧ ((p2 → False) ∧ (p5 ∨ (p1 → (p5 → True))))) → p4) → (p4 ∧ (((True ∧ p5) → p2) ∧ p4))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337662977974108921905521251718 : (p1 → (((((True ∧ p3) → ((p4 ∧ False) → p2)) → (True ∨ p1)) → (((p3 ∧ True) ∨ False) ∨ p5)) ∨ (p4 → ((p3 → (p3 ∧ p2)) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234768201530157904849448392964 : ((p4 → (p5 → p1)) → (((p1 ∧ p5) → (p2 ∧ True)) ∨ ((((((p1 ∨ False) ∧ False) ∨ (p5 ∨ (p4 ∨ (p2 ∨ p5)))) ∧ p2) ∨ True) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309359437138344106755627381954 : (p2 ∨ ((((False ∧ p4) → ((p5 → True) ∨ p3)) ∧ (((p5 ∧ True) ∨ (((True → p4) ∨ ((p5 → p2) ∧ False)) ∧ p2)) ∧ p4)) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152447535266559088489671381547 : ((((p5 → p5) → False) ∧ ((p1 ∨ False) ∨ ((p3 ∨ (p1 ∧ ((p3 ∨ (False ∧ (p2 → False))) ∧ p3))) ∨ False))) → (p2 ∧ (p1 ∨ (p2 → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : (p5 → p5) := by
        -- Implications on the right can always be decomposed.
        intro h7
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h8 := h2 h6
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h13 : (p5 → p5) := by
          -- Implications on the right can always be decomposed.
          intro h14
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h15 := h2 h13
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h21 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h22 : (p5 → p5) := by
            -- Implications on the right can always be decomposed.
            intro h23
            -- One of the premise coincides with the conclusion.
            exact h23
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h24 := h2 h22
          -- False on the left can always be used.
          apply False.elim h24
        case inr h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- False on the left can always be used.
          apply False.elim h26
    case inr h28 =>
      -- False on the left can always be used.
      apply False.elim h28
  -- Conjunctions on the left can always be decomposed.
  let h29 := h1.left
  let h30 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h30
  case inl h31 =>
    -- Disjunctions on the left can always be decomposed.
    cases h31
    case inl h32 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h32
    case inr h33 =>
      -- False on the left can always be used.
      apply False.elim h33
  case inr h34 =>
    -- Disjunctions on the left can always be decomposed.
    cases h34
    case inl h35 =>
      -- Disjunctions on the left can always be decomposed.
      cases h35
      case inl h36 =>
        -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
        have h37 : (p5 → p5) := by
          -- Implications on the right can always be decomposed.
          intro h38
          -- One of the premise coincides with the conclusion.
          exact h38
        -- We have shown the premise of h29, we can now drive its conclusion.
        let h39 := h29 h37
        -- False on the left can always be used.
        apply False.elim h39
      case inr h40 =>
        -- Conjunctions on the left can always be decomposed.
        let h41 := h40.left
        let h42 := h40.right
        -- Conjunctions on the left can always be decomposed.
        let h43 := h42.left
        let h44 := h42.right
        -- Disjunctions on the left can always be decomposed.
        cases h43
        case inl h45 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h41
        case inr h46 =>
          -- Conjunctions on the left can always be decomposed.
          let h47 := h46.left
          let h48 := h46.right
          -- False on the left can always be used.
          apply False.elim h47
    case inr h49 =>
      -- False on the left can always be used.
      apply False.elim h49



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319852454439910653503376621063 : (p4 ∨ ((((p2 ∨ p5) → p2) ∧ p1) ∨ (p5 ∨ ((True → p1) ∨ (((True → False) → (True ∨ False)) ∨ ((p3 → ((False ∨ False) ∧ p4)) ∨ p2)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317720496121227607765152865260 : (p4 ∨ ((((p2 ∧ p1) ∧ (p2 ∧ (p2 → ((((True ∨ p5) ∧ (p3 → (p1 → (True → (p4 ∧ p4))))) ∧ p5) ∧ False)))) → (p2 → False)) ∨ p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h4.left
  let h8 := h4.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720284160126235794785886256738 : ((((((p1 ∨ p5) ∧ p5) ∨ p2) → ((True ∧ ((p3 ∧ True) ∨ (False ∧ ((((p4 ∧ (p2 ∧ False)) → p5) ∨ p2) ∨ (p3 ∨ p3))))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224560649109489528855070950275 : ((p2 → (p3 ∨ True)) ∧ (((p1 ∧ p5) ∨ True) ∧ (((p3 → (((p3 → ((True → False) → (False ∨ p2))) ∨ True) ∨ False)) ∧ (True ∨ p2)) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200022092680933567959444573971 : ((((p1 ∧ p4) → (p3 ∧ p3)) → (p4 ∧ False)) → ((p3 → (((p2 → p2) → (p5 ∨ p4)) ∨ p5)) ∨ (((True ∧ p1) ∧ p3) ∧ (True ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p1 ∧ p4) → (p3 ∧ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Conjunctions on the left can always be decomposed.
    let h7 := h4.left
    let h8 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h3
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248029978635470879332344775888 : ((p1 ∨ p5) ∨ ((((p3 ∨ ((p2 ∨ p3) ∨ p1)) ∧ ((True ∧ p4) ∧ (False ∧ (True → (False ∧ (p3 ∨ p5)))))) ∧ p4) ∨ ((p2 ∧ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672630858042022562478047287357 : (((((((((True ∧ False) ∨ p2) ∧ False) → ((p5 ∧ (True ∧ (p3 ∨ True))) ∨ (p1 → False))) ∨ p3) ∨ (p3 → p1)) → ((p4 ∨ p4) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183862937733748229275817189470 : (((((p3 → (p4 ∨ p5)) ∧ p2) ∨ (False ∨ (p1 ∨ True))) ∧ p4) ∨ ((p2 ∧ p3) ∨ (True ∨ (True → ((p4 → (True ∨ (False ∧ p5))) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325854380296931426925033886774 : (p5 ∨ (p4 ∨ (((p3 → (False ∨ (((p1 → True) ∧ ((p2 → ((p1 → p2) ∨ (p5 ∧ p1))) → (p1 ∧ (p2 → p3)))) ∨ p2))) ∨ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657225735105778405110752306595 : ((((((p4 → p4) → p3) → (False ∨ ((p1 ∧ p4) ∨ (False ∧ ((p5 ∨ (((p1 ∧ p3) ∨ True) → p2)) ∨ (p4 → True)))))) ∨ (False → p3)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_316926969657964245798182304291 : (p3 ∨ (p2 → ((((p3 ∨ (True ∧ ((((p2 ∨ (p1 ∨ False)) → p1) ∧ (True → (p3 ∨ p4))) ∨ False))) ∨ p2) ∨ p3) ∧ (True ∧ (True → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350128618764981578795112178878 : (p4 → (((p5 → (((p4 ∨ p5) → p4) ∨ (((True → p4) → (p2 ∨ False)) ∨ (p1 ∨ False)))) → ((((p5 ∧ p2) ∧ p2) ∧ p5) ∧ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265784380803478315319641439663 : (True ∧ (p4 ∨ ((p3 ∧ (p1 → (False ∧ p4))) → (((True ∧ (True ∧ (p1 ∨ ((p5 → (p3 → (p1 ∧ p4))) ∧ p5)))) ∧ True) → (p1 ∧ p1))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  cases h8
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h1.left
    let h16 := h1.right
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h17 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h18 := h13 h17
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h19 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h20 := h18 h19
    -- We need to get the left conjuct of h20 based on <expert-advice>.
    let h21 := h20.left
    -- One of the premise coincides with the conclusion.
    exact h21
  -- Conjunctions on the left can always be decomposed.
  let h22 := h2.left
  let h23 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h24 := h22.left
  let h25 := h22.right
  -- Conjunctions on the left can always be decomposed.
  let h26 := h25.left
  let h27 := h25.right
  -- Disjunctions on the left can always be decomposed.
  cases h27
  case inl h28 =>
    -- Conjunctions on the left can always be decomposed.
    let h29 := h1.left
    let h30 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h28
  case inr h31 =>
    -- Conjunctions on the left can always be decomposed.
    let h32 := h31.left
    let h33 := h31.right
    -- Conjunctions on the left can always be decomposed.
    let h34 := h1.left
    let h35 := h1.right
    -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
    have h36 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h33
    -- We have shown the premise of h32, we can now drive its conclusion.
    let h37 := h32 h36
    -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
    have h38 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h34
    -- We have shown the premise of h37, we can now drive its conclusion.
    let h39 := h37 h38
    -- We need to get the left conjuct of h39 based on <expert-advice>.
    let h40 := h39.left
    -- One of the premise coincides with the conclusion.
    exact h40



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165214249616952071745204144885 : (((((p4 ∨ (p3 ∨ True)) ∧ (p5 ∧ (p2 ∨ (p4 → p3)))) → (p4 → p2)) ∨ (True ∨ p2)) ∨ ((((p3 ∧ p3) ∨ p4) ∧ (p4 ∨ False)) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50330346455145330591049855270 : ((((p1 → ((((p4 ∧ True) ∨ p3) ∨ p3) ∨ p2)) ∧ (((p2 ∨ p2) → ((p1 → False) ∨ p1)) ∧ p2)) ∨ ((True → (p5 ∨ p2)) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673782030384107158600728249993 : (((((p3 ∧ True) ∨ (True ∧ ((p2 ∨ (p2 ∨ ((p3 ∨ True) ∧ (((False → (p1 → False)) → p2) ∧ p5)))) ∨ p3))) → ((p3 ∨ p1) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151586396701913535342734597074 : (((((((True → False) → False) ∨ (p4 → p2)) ∨ p2) → ((p5 ∨ (p4 ∧ (p3 ∨ p3))) ∧ p2)) → (p5 ∧ p1)) → ((p1 → p3) ∨ (True ∧ True))) := by
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
theorem thm_5_vars_782398586991629114631804220009 : (((p3 ∨ ((((((p5 ∧ p3) ∧ p2) ∨ p3) → ((p4 ∨ p3) ∧ (p4 → ((True → p1) ∧ (((False ∨ False) ∧ p3) ∨ p5))))) → p2) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_263725231246721380338180902084 : (True ∧ (((p4 → ((p3 → (False ∨ (((p4 → (False ∧ p1)) → True) ∨ (p3 → p2)))) ∧ False)) → True) → (p1 → ((p5 → (p5 → p1)) ∧ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247322953293825128880923375732 : ((False ∨ False) ∨ (True ∧ ((((False ∧ (p1 → True)) ∧ (p2 ∧ (p1 ∨ p3))) ∨ p2) ∨ (True ∧ (True ∨ (((False ∨ (p4 ∧ False)) ∧ p3) ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41151401769288597793370757712 : (((((p1 ∨ p1) ∧ ((((p3 → p4) ∨ (((p2 ∨ (p5 ∨ True)) → False) ∨ p2)) → (p1 ∨ True)) ∨ p3)) ∨ (p1 ∨ (False → p4))) ∨ p5) ∨ p3) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175369689606000326888938093175 : ((True → ((p3 → ((p3 → (p1 ∨ ((True ∨ p4) ∧ False))) → (p3 ∧ p2))) ∧ p1)) → (((((False ∨ True) ∧ p1) ∨ p4) ∨ (True ∧ p4)) ∨ p1)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193079157131622530480472706432 : ((((p3 ∧ p1) ∧ (p5 ∨ True)) ∧ (p1 ∨ (p4 ∨ False))) → ((p2 ∨ (p4 ∧ p2)) ∨ ((((((False ∨ p5) ∨ p2) ∨ True) ∨ p2) → p2) ∨ p3))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263612685222102365123595866413 : (True ∧ ((((p2 ∨ ((False → (p4 ∨ (p3 ∧ p2))) ∨ (p3 → p4))) → p2) ∧ (False ∨ (False ∨ (p3 → p1)))) → (((p5 → p4) ∨ p4) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_463704504249942359713890532035 : ((((p5 ∨ ((p1 ∧ False) ∧ ((True ∧ (p1 ∧ p4)) ∧ (p2 → (p3 ∨ (p4 ∨ p1)))))) ∨ (True ∨ ((False ∧ ((p5 ∧ p2) ∧ p4)) → p2))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623479860653669543774719630525 : ((((False ∨ (((p2 ∧ p3) ∧ (p2 → ((p5 ∧ p4) → ((p2 ∨ p3) ∨ (p3 → (p3 ∨ p2)))))) ∨ (p4 ∧ (p2 ∨ (p1 ∨ p2))))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308354853892862965771422874426 : (p2 ∨ ((((p5 ∧ p5) → ((p1 → ((p3 ∧ p5) ∨ (p5 ∧ p1))) ∧ (((p5 → (False → p4)) → p1) ∧ ((True ∧ p1) → False)))) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759921221641825219637868211333 : (((p2 ∧ (((p1 ∨ (p1 ∧ (True ∨ p1))) ∧ True) → ((((((p5 ∨ p2) ∨ p4) → p5) → True) ∧ ((p3 → p5) ∨ (False ∧ p4))) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_974573975094247183261194184638 : ((((p1 → p1) → ((((p1 ∨ p1) ∧ (p3 ∨ (False → p1))) ∨ p4) ∧ (((False → (((p3 ∧ False) → (p4 ∨ p4)) ∧ True)) → p3) ∧ False))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748242264029631236908160419924 : ((((p2 → True) → (((p5 → p1) → (p3 ∧ ((p2 ∧ True) ∧ p3))) → (((False → (p5 ∨ (p5 ∨ p3))) → (p4 → (p4 ∨ p4))) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315481011977318294326502376934 : (p3 ∨ (((p4 ∨ p1) → p2) → ((((((False → True) → p1) ∧ p3) ∧ p1) → (((p5 → (p4 ∧ p5)) → False) ∨ (p3 → (True → p2)))) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : (p4 ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h9
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230306112920834099274990909812 : (((p1 ∨ p2) ∧ p4) → (p5 ∨ (((p4 → False) → (p1 → p2)) ∧ ((p1 ∧ (((p2 ∧ (p1 ∧ p2)) ∧ p5) ∧ (p4 ∨ (p2 → p2)))) ∨ p4)))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- False on the left can always be used.
    apply False.elim h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



