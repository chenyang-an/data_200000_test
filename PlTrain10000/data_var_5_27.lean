variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48726806648967762917123498872 : (((((p5 ∨ p1) ∧ p2) ∧ ((p2 ∨ (p3 → ((p2 ∨ p3) ∧ (p5 ∨ p5)))) ∧ ((True ∧ (p4 → p2)) ∧ True))) ∧ (p4 ∨ (p5 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669983938873697591492933209101 : ((((((True ∨ p5) ∨ (p3 ∧ (((p1 → p4) ∨ p5) ∧ p3))) → (False ∧ (True ∨ ((True → p4) → (p4 ∧ p1))))) ∨ ((p4 ∧ p3) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_258177479562384201094144514538 : ((p4 ∨ p4) → (((((p5 ∨ False) ∧ (p5 → (p2 ∧ (False ∨ (p2 → p1))))) ∧ p5) ∧ p1) ∨ (True → ((p2 ∧ p1) → ((True ∨ p4) → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h4.left
      let h8 := h4.right
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h4.left
      let h11 := h4.right
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Implications on the right can always be decomposed.
    intro h14
    -- Implications on the right can always be decomposed.
    intro h15
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h14.left
      let h18 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h14.left
      let h21 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610643745993784719400626733312 : ((((((((p2 → (False ∨ p1)) → p3) → ((((((p4 → True) → (p3 ∨ False)) ∧ p3) → p4) ∨ True) ∨ p1)) → (p4 ∧ p2)) → p2) ∨ False) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 → (False ∨ p1)) → p3) → ((((((p4 → True) → (p3 ∨ False)) ∧ p3) → p4) ∨ True) ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114057349403948949787180523301 : ((((((p2 ∨ ((p1 ∨ p5) → (p2 → False))) → (p5 ∧ True)) → p2) ∨ ((p2 → (p5 ∨ p2)) → p3)) ∨ (True ∧ (p4 ∧ p1))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694984417856777886739973996876 : ((((((((True ∨ True) → ((p2 ∧ p1) → False)) ∧ p1) → (p3 ∨ p2)) ∧ p5) → ((p4 ∨ (p3 → p1)) ∨ ((False ∧ p3) → (p3 ∧ p2)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h7 := h4.left
  let h8 := h4.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158393962251034853112734861173 : (((p3 → p3) ∧ (p4 ∨ ((((p4 ∨ True) → (p1 → (True → p1))) ∧ (False ∨ (p3 ∨ True))) → p5))) ∨ (((True → p2) → True) ∨ (p2 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250952493652203194202032950317 : ((p1 → p4) ∨ (((p5 ∨ ((True ∧ ((p4 → p2) ∧ p5)) → (True ∨ p1))) ∨ False) → (((p4 ∧ (p3 → p4)) → (p4 ∧ p4)) ∧ (p2 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
  cases h1
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14
  -- Implications on the right can always be decomposed.
  intro h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41420547278104568428770486364 : ((((p1 ∨ ((p1 → (False → ((p1 ∧ (False → (p3 → p2))) ∨ p5))) → p3)) ∨ (p3 ∨ (((p1 ∧ p5) ∧ (p2 ∨ p2)) → p1))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185275553233397613013515457797 : ((p1 ∧ (p5 → (p5 → (p1 ∧ (False ∧ (p3 ∨ (p3 ∧ p5))))))) ∨ (((p3 → p1) ∧ ((p3 ∧ True) ∧ (True ∧ p5))) → ((p4 → p1) ∨ p1))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h10 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h11 := h2 h10
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337383356196840910566422238139 : (p1 → (((p3 → p5) → ((((p1 ∨ p1) → (p3 → True)) → (True ∨ p4)) → (((p1 → (p5 → p3)) → p2) → p2))) ∨ ((True ∨ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140059386599897614898169696972 : (((((((p4 → p3) ∨ False) → p4) ∨ p5) → ((p3 → (False → (((p5 ∨ p3) ∨ p5) ∧ p2))) → p4)) ∨ (False ∨ p4)) → ((p5 ∧ p2) → p4)) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : ((((p4 → p3) ∨ False) → p4) ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (p3 → (False → (((p5 ∨ p3) ∨ p5) ∧ p2))) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h10
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h11 := h7 h8
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158675470734117132648488233376 : ((p2 ∧ (((p2 ∨ False) ∨ (((p1 → (p3 ∧ True)) ∨ p1) ∧ ((p2 ∧ False) → (p3 → p5)))) → p5)) ∨ (False → (((p3 ∨ p1) ∨ p3) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227348521409727592544236062881 : (((p3 → p1) → p5) ∨ ((((((p2 ∨ (True ∨ (((False ∧ p2) → True) ∧ p5))) → p4) ∧ ((False → p3) ∧ (True ∨ p1))) ∧ p2) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221389625457641031273090020106 : (((True → True) ∨ False) ∧ (((((False ∨ ((p3 ∧ False) ∨ p2)) → p4) → ((p3 → (False → ((True ∧ (p5 → True)) → p3))) ∧ p1)) → p5) ∨ True)) := by
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
theorem thm_5_vars_134184499759020627168780193874 : ((((((p5 ∧ (p2 ∨ False)) ∧ ((False ∧ True) ∧ p5)) ∧ (True ∨ True)) ∨ (p5 ∧ (p5 ∧ ((p4 → p3) → p3)))) ∨ True) ∨ (False ∨ (p1 ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345410516520446363335529138508 : (p3 → (((((p1 ∨ ((p3 ∧ (True ∨ p3)) ∧ p1)) ∨ p3) ∧ ((((p2 → False) ∨ (p4 ∨ ((True → p3) ∧ p3))) → p4) → p4)) → p4) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137513597438183460146972946812 : ((p5 ∧ ((False ∨ ((False → (p2 ∨ p4)) ∧ p5)) ∨ ((p3 → ((p1 ∨ p1) ∨ (p5 → p2))) → (False ∧ (True ∨ True))))) ∨ ((False ∧ p5) → p2)) := by
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
theorem thm_5_vars_66145954786361346798003086050 : ((p5 ∨ ((p2 → ((((p4 ∨ ((((p2 ∧ ((p5 ∨ p5) → p3)) → p3) ∧ True) → (p1 → p3))) ∨ p2) ∨ True) → p5)) ∨ (p4 → p4))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150272542819529202419246027590 : ((p3 → (p2 ∨ ((p4 ∧ p5) ∧ (False ∧ (((p3 ∨ ((p1 ∧ (p5 → (p1 ∨ True))) → p2)) ∨ p4) ∧ False))))) ∨ (p4 → ((p1 ∨ True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184776084648112696827708869082 : ((((p4 ∨ (p2 ∨ p1)) ∧ False) ∨ ((p2 ∧ p3) ∧ (p2 → p3))) ∨ ((((False ∨ p5) ∧ p2) → ((p2 ∨ p2) → (p5 ∧ p5))) ∨ (p2 ∨ False))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h12
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h1.left
    let h15 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h1.left
    let h20 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- One of the premise coincides with the conclusion.
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40665797063586840148607790364 : ((((((p4 → ((p3 ∧ ((True → True) → p4)) → ((p2 → (((p2 ∧ p1) ∧ p3) ∧ p2)) → p5))) ∨ p4) → (True → p1)) → p4) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67985910312418234319695975687 : ((p2 → ((p1 ∨ p4) ∧ ((p2 → (((p1 → ((p3 ∨ p5) ∧ False)) → (p5 ∧ (True ∨ p4))) ∨ p3)) ∨ ((p3 → (p3 → p3)) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147364193190694004852603333437 : ((((p4 → ((((p4 ∨ p5) ∧ False) ∨ p2) ∨ (p5 ∧ ((p5 ∨ p5) → True)))) → (p1 ∨ (False ∨ p1))) ∨ False) ∨ ((p4 → p4) ∨ (False ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37189269019421412895659796663 : (((((((False → (p3 ∧ False)) → (p3 ∨ False)) ∧ p5) ∨ (False → ((((p4 ∨ (p4 ∨ p2)) ∨ p2) ∨ (p4 ∨ False)) ∧ p1))) ∧ p2) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197475334468591565150959563747 : ((((p5 ∧ p1) ∨ (False → p4)) ∧ (False ∧ p5)) ∨ (p1 → (((p4 → p3) ∧ False) ∨ (p1 ∧ ((p1 ∨ False) → (((True ∧ p1) ∨ p5) ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615088750303248428617674534669 : (((((p5 → ((((p1 ∨ False) ∨ (p3 → ((p5 ∧ (False ∧ p4)) ∧ p1))) ∨ (p1 → True)) ∨ p3)) → ((False → (False ∧ True)) ∧ False)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68335043050799451901164566328 : ((p3 → ((p3 ∨ ((((p3 → (p4 ∨ (p5 → True))) → p4) → False) ∨ (p4 ∧ False))) → ((False ∨ p1) ∨ (p2 ∨ (p4 → (True ∨ True)))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133785377391862319905382251531 : (((((p5 → True) ∨ p2) ∧ ((p5 → (False → p2)) ∧ (p2 ∨ ((p4 ∧ p1) ∨ ((p5 ∧ p2) ∧ (True → p3)))))) ∧ p1) ∨ ((p5 ∧ p2) → p5)) := by
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
theorem thm_5_vars_784313343247828157706260825003 : (((p3 ∨ (p1 ∧ (True ∧ (p4 ∧ (p1 → ((((True ∧ p5) → ((((True → p5) ∧ p4) ∨ p5) ∧ (p1 ∧ (p4 ∧ p2)))) ∨ True) ∨ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809798146259142166921849699344 : (((p5 → ((True ∧ ((((p3 ∨ (p2 → True)) → p5) ∧ p2) → (((p5 ∨ ((False ∧ p3) → p3)) → (p2 ∧ p4)) ∨ False))) ∨ (p2 → p5))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248027685408532094681733041750 : ((p1 ∨ p5) ∨ ((((((p5 → p3) ∨ (p2 ∧ (p4 ∧ (p3 ∧ p5)))) ∨ False) ∨ (p3 → (p3 → ((False ∧ False) → p4)))) ∨ p2) → (p5 ∨ True))) := by
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
          -- Conjunctions on the left can always be decomposed.
          let h7 := h6.left
          let h8 := h6.right
          -- Conjunctions on the left can always be decomposed.
          let h9 := h8.left
          let h10 := h8.right
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47643299533560586050339024958 : (((((((((True ∧ True) ∧ p3) → p2) ∧ (p2 → (True → (p4 ∧ (p2 ∨ (p4 ∧ p2)))))) ∨ (p4 ∨ p1)) → p4) ∧ p3) → (p2 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324261496302563321400002184012 : (p5 ∨ ((((p2 ∧ (p1 ∨ p1)) ∨ p2) ∨ (p5 → p5)) ∨ (False ∨ (((False → p2) ∨ (((p3 → p1) ∧ p4) ∨ p1)) → (p3 ∧ (p5 ∧ p1)))))) := by
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
theorem thm_5_vars_63349405882036852351810463014 : ((p5 ∧ (p1 ∧ ((p2 → (p1 ∧ ((p1 ∧ (((p5 ∨ (p3 ∨ p2)) ∨ p5) ∧ (p2 → (p5 ∨ ((p5 ∨ p3) ∨ p3))))) ∧ p3))) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186478719965026884322044637581 : (((((p3 → p2) ∨ True) ∨ ((p4 ∧ False) ∨ False)) ∧ (True → False)) → (p4 ∨ (p5 ∧ ((p1 ∧ p2) ∨ (((p1 → (p3 ∧ p3)) ∨ False) → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h7 := h3 h6
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h9
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_436522554504432262699854341453 : (((((p3 → (p2 → p3)) → ((p1 ∧ p2) ∧ ((((p4 → ((p3 → p3) → p2)) ∨ (p4 → True)) ∧ (p2 ∧ True)) ∧ False))) → (p5 ∧ p3)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → (p2 → p3)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (p3 → (p2 → p3)) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h8
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- False on the left can always be used.
  apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230770018631256165009083610901 : (((True ∧ p1) ∨ p1) → (((p5 ∧ p3) ∧ (((p3 ∨ (p2 ∧ (p2 → (p4 ∨ True)))) → p5) ∨ (p4 ∨ (p2 → p1)))) → (p2 ∨ (True ∧ p5)))) := by
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
  cases h4
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7928157768905787604336636785 : ((((p3 → (p5 ∨ ((False → ((p5 ∨ p3) ∨ (p2 ∧ (((p2 → p5) ∧ p5) → p5)))) → (((p2 → p1) → p5) ∧ p3)))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48375135238719035834964135518 : (((p5 ∨ (p1 → (((p1 ∨ p2) → ((False ∨ p4) → (p3 ∨ (p3 → (p3 → ((True ∧ p1) ∨ p3)))))) ∧ (p1 ∨ p4)))) → (True ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173069144475363856408655467030 : ((False ∨ (False ∨ (((p2 → (p1 ∨ p1)) ∨ True) ∧ (((p5 ∨ True) → False) → False)))) ∨ ((((p3 ∨ (p3 ∨ True)) ∨ True) → (p3 → p3)) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345394302781217342813428274342 : (p3 → (((((False → (((False ∧ (p1 ∨ p2)) ∨ ((False ∨ True) ∧ (((p5 ∧ p4) → (p1 → p4)) → False))) ∨ p1)) ∧ p3) ∨ True) → p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111752315920685938004871958048 : ((((p4 → (((p2 → p1) ∨ ((p5 → p2) ∨ ((False ∨ True) ∧ p3))) → (True → (False ∧ (p5 → (p3 ∧ True)))))) → p5) ∨ p1) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148220484058143808167665415748 : ((((p3 ∧ ((p5 ∨ p5) ∨ (True → (((False → p2) ∧ (p4 ∨ p4)) ∨ p1)))) ∧ p3) ∨ (p2 → (p5 → p5))) ∨ (p5 ∨ ((p3 ∨ p2) ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38231035676785004898035979144 : ((((True → ((p3 → p1) ∨ (False → (((p1 ∧ (p3 → (p1 → p1))) ∧ p5) ∧ (p2 → (p1 → p4)))))) → (p3 ∧ (p2 ∨ False))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113646278939515404846913035264 : ((((((False ∧ (False ∨ ((True ∧ False) ∧ True))) → ((False ∨ (False ∨ p2)) ∧ (False → p2))) → (p5 ∧ p2)) ∧ True) → (p4 ∨ p1)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164779731957087036329891155246 : ((((p3 → (p5 ∧ ((True ∧ p5) ∧ False))) ∧ (p3 ∧ ((p3 ∧ (p3 ∧ False)) ∨ True))) ∨ p3) ∨ ((((p5 ∨ True) → p5) → p5) ∨ (p3 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310536576638312431654657943992 : (p2 ∨ ((((False ∧ p3) ∧ True) → (False ∨ p1)) → ((((False → (p1 → p1)) ∨ p1) ∨ p5) → (p3 → (((p2 ∧ p1) → (p1 → False)) ∨ p3))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262304208570199921675637126011 : (True ∧ ((((p5 → ((p5 ∧ ((True ∨ True) → (p4 → p4))) ∧ False)) → False) ∨ ((p3 ∨ (((p5 → p1) ∧ (p4 ∨ p1)) ∧ p1)) ∧ p4)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152474355051210132666282243207 : (((p5 → (p1 → p2)) ∧ (((p1 → p2) ∨ ((p2 ∨ p2) ∨ p5)) → (p4 ∧ (p2 ∨ ((p5 ∧ p5) ∨ p3))))) → (p2 → ((p4 ∧ p2) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((p1 → p2) ∨ ((p2 ∨ p2) ∨ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47530652868547983191446429503 : (((p4 ∨ (((p4 ∧ (((((((True ∧ True) ∨ False) → False) ∨ True) ∧ p4) → p2) → (p5 ∨ p2))) ∨ p3) ∨ (p4 ∧ p3))) ∨ (p1 → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300621300123649024570614035843 : (False ∨ ((p1 → ((p4 ∧ ((p3 ∧ False) → p2)) ∧ (p1 ∨ (((False → p1) ∧ True) ∧ (p4 ∧ (p3 → p2)))))) → ((p1 ∨ p4) ∨ (p1 → True)))) := by
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
theorem thm_5_vars_312367954242099546828729638756 : (p2 ∨ (p3 → ((((p4 ∨ (p3 ∧ p5)) ∧ ((False ∧ (False ∨ (False → (p4 ∧ (False → True))))) ∧ p3)) ∨ p5) ∨ (((p4 → p3) ∨ True) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_167283354401839788673241167823 : (((((False ∧ (False → (p4 → p2))) ∧ (((True ∧ (True → p5)) → p4) → False)) ∨ False) → p4) → ((p3 → p2) ∨ ((p4 ∨ (True → p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43521961542009388629576379015 : ((((p5 ∨ (p3 ∧ (((False ∧ (((p5 ∨ (p5 ∧ True)) ∨ (p1 ∧ p3)) ∧ True)) ∨ p1) → ((p3 ∧ True) ∨ (p1 ∨ False))))) ∨ True) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742765730516706339343096401303 : ((((p3 → False) ∨ ((True ∧ (p2 → (p3 ∨ ((((p5 ∨ p4) ∧ ((p5 ∧ p5) ∧ p3)) ∨ p3) → (p5 ∨ p2))))) → (p1 ∨ (True ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136398622795792576025388235353 : (((p1 ∨ (p1 → (p3 → p4))) ∨ (p5 ∧ (True ∧ (True → (p4 ∧ (p5 ∨ (((p2 ∨ p4) ∧ (p5 ∨ p4)) ∧ p3))))))) ∨ (p2 ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207454714410233549454851175678 : (((p5 ∨ ((p5 ∨ p4) ∨ True)) ∨ p2) → (p3 ∨ (((p5 ∧ p2) → p5) ∨ (p1 ∧ (((p4 → p3) ∧ True) ∧ (True ∨ ((False ∧ p2) → p3))))))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h10
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h14
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- One of the premise coincides with the conclusion.
          exact h15
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h18
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- One of the premise coincides with the conclusion.
        exact h19
  case inr h21 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h22
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- One of the premise coincides with the conclusion.
    exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151807450392314365617229441304 : ((((True ∨ ((p4 ∧ (((True → p5) → (True ∧ p4)) → p1)) ∧ p2)) → False) ∧ ((False ∨ (p3 → p3)) → p5)) → (((False ∧ False) ∧ True) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ ((p4 ∧ (((True → p5) → (True ∧ p4)) → p1)) ∧ p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50720102679223765794017680696 : ((((p5 → p2) ∨ (((((p5 ∧ False) ∧ p5) → p1) ∨ ((p4 → True) ∧ (False → (p3 ∨ False)))) ∧ p1)) → (p2 ∨ (False → (False ∨ False)))) ∨ p5) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- False on the left can always be used.
      apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42503927556768834396371071815 : (((False ∨ ((False ∨ ((((((p2 → p1) ∧ True) ∨ p2) ∨ False) ∧ p2) ∧ (True → True))) → ((((p3 ∧ p1) → p4) ∨ p2) ∨ p5))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173104064947718970470629735609 : ((p1 ∨ (p4 → (p2 → (((p3 ∨ ((p5 ∧ p1) ∧ p3)) ∧ p5) ∨ (p4 → p4))))) ∨ (p1 → (p4 ∧ (p1 ∨ (((p3 ∧ p2) ∨ p4) ∧ True))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143047507096717353487034161739 : ((False → (((p1 → ((p1 ∧ (p1 → ((True ∨ p3) → p5))) → (False ∧ p2))) ∧ ((p1 → p4) ∨ (p3 ∧ True))) → p2)) → (p2 → (p2 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215404152128056925169115921846 : ((p2 ∧ (p5 ∨ (p5 → p5))) ∨ ((p5 ∨ (p5 ∧ False)) ∨ (True ∨ ((p1 ∧ ((p3 → p2) ∨ ((p1 ∧ (True ∧ p5)) ∧ True))) ∨ (True ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216049052552292260237563618790 : ((p5 ∨ (p2 ∧ (p4 ∨ p2))) ∨ (((p3 → (p1 ∨ True)) ∨ ((((False → True) → False) → p2) ∨ p2)) ∨ (True ∧ (p3 ∨ ((True ∧ p5) ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_41264836167788255826195796426 : ((((p1 ∧ ((((p5 ∨ True) ∨ p5) → (((p5 ∧ (False → False)) → False) ∨ True)) → (p2 → p4))) ∨ (p5 ∨ (False → (p5 ∧ p4)))) ∨ p2) ∨ False) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645877801353919721352375522850 : ((((True → ((((True ∨ (False ∨ (p3 → ((p3 → ((p2 → ((p2 ∨ False) ∧ p2)) → (p5 → p5))) → p4)))) ∧ True) → p1) ∨ True)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243774826477209339637060967926 : ((p5 → p5) ∧ ((((p3 ∧ (((p1 ∨ (p5 ∨ p5)) → (p1 ∧ (((True → True) ∨ p5) → p5))) ∧ (False ∧ p3))) ∧ False) ∧ p4) ∨ (p1 → p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153005017552449523113768113032 : ((p2 ∧ ((((((p3 ∧ p4) ∨ p4) ∧ p5) ∨ ((False → p3) ∨ (p2 ∨ p2))) ∧ (p2 → (p2 ∧ p5))) ∧ p5)) → (p1 ∨ ((p1 ∨ p2) → p5))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h20 =>
        -- One of the premise coincides with the conclusion.
        exact h5
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h25 =>
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h28
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h29 =>
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h30 =>
          -- One of the premise coincides with the conclusion.
          exact h5
      case inr h31 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h32
        -- Disjunctions on the left can always be decomposed.
        cases h32
        case inl h33 =>
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h34 =>
          -- One of the premise coincides with the conclusion.
          exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174104889997826002569575437630 : ((((True ∨ p3) ∨ ((((p2 → p5) → p4) → (True → False)) ∨ True)) ∧ (True → False)) → ((((p5 → p1) → (True ∧ p5)) ∨ (p4 ∨ p1)) ∧ False)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h7 := h3 h6
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h9
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h14 := h3 h13
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h17 := h3 h16
      -- False on the left can always be used.
      apply False.elim h17
  -- Conjunctions on the left can always be decomposed.
  let h18 := h1.left
  let h19 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
      have h22 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h19, we can now drive its conclusion.
      let h23 := h19 h22
      -- False on the left can always be used.
      apply False.elim h23
    case inr h24 =>
      -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
      have h25 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h19, we can now drive its conclusion.
      let h26 := h19 h25
      -- False on the left can always be used.
      apply False.elim h26
  case inr h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
      have h29 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h19, we can now drive its conclusion.
      let h30 := h19 h29
      -- False on the left can always be used.
      apply False.elim h30
    case inr h31 =>
      -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
      have h32 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h19, we can now drive its conclusion.
      let h33 := h19 h32
      -- False on the left can always be used.
      apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69049577201350974253870896053 : ((p5 → (((False → p2) → (p5 ∧ ((p2 → (p2 ∧ p4)) ∨ ((((False → p5) ∧ p5) → p3) ∧ (p5 → (p4 ∧ (p5 → p5))))))) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103140932686451651852135999766 : ((((False → p1) ∧ (p1 → (((True ∨ p2) → ((((p2 ∧ True) → (p3 ∧ True)) → p2) ∧ False)) → ((p5 ∨ True) → p3)))) ∨ p4) ∧ (p5 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : (True ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : (True ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  -- Implications on the right can always be decomposed.
  intro h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112613791000148356145942137573 : (((((((p2 → p3) ∧ (p4 → False)) ∨ p1) ∨ (((False ∨ (p2 → False)) ∨ p5) ∧ ((p2 → False) → p3))) ∨ (p4 ∨ p3)) → p1) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263392461422854480841185623991 : (True ∧ (((((True → p4) ∨ ((p5 ∨ False) ∨ (False → (((p3 ∧ p4) → True) → p5)))) ∧ p2) ∨ (False ∨ (p5 ∨ True))) ∨ (False ∨ (p1 → p1)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165357551083448523616432135629 : (((p4 ∨ (((((p3 → (True → p5)) → p4) ∧ p5) ∨ p1) ∨ True)) ∧ ((p1 → p4) ∨ p3)) ∨ (p4 ∨ ((p3 ∨ True) → (p5 → (True ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699118810364082614857095177384 : ((((p5 ∨ (p4 → (((p1 → p2) ∨ p3) ∨ ((False ∨ p5) ∧ False)))) ∨ (((((p1 ∨ p5) ∨ p3) ∨ (False → p1)) ∨ p2) ∨ (p2 ∧ p4))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_864055767984797134159039343108 : (((((((p4 ∨ ((False ∧ (False ∧ False)) ∧ p5)) ∨ p3) ∨ p5) ∨ (((True ∧ True) ∨ (((p5 ∧ (p5 → p5)) → p5) ∨ p1)) ∨ p4)) → False) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p4 ∨ ((False ∧ (False ∧ False)) ∧ p5)) ∨ p3) ∨ p5) ∨ (((True ∧ True) ∨ (((p5 ∧ (p5 → p5)) → p5) ∨ p1)) ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117411756113033124446670046687 : ((p1 ∧ ((False → ((p5 ∨ True) ∧ ((p3 ∧ (((p4 ∨ True) ∧ p3) ∨ (((p4 → (p5 → p1)) ∨ p2) ∧ p1))) ∧ False))) → False)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152839355490497364619387082252 : (((False → p3) → ((((p5 → p1) ∨ False) → p4) → (((False ∧ (False → p3)) ∨ p2) ∨ ((p5 ∧ p5) ∨ False)))) → ((p4 → p1) ∨ (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720949936931873339023190760889 : (((((p2 ∨ p5) ∧ (p3 ∨ p4)) → (((True ∨ p4) ∧ p3) → (((p3 → ((p1 → p2) → (False → (p2 → p5)))) → (True ∧ True)) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681250521578681343028925714256 : ((((p4 ∧ (False ∨ (((p1 ∨ (p1 ∧ p3)) ∨ (p3 ∨ p3)) ∧ (True ∧ (p1 ∨ (p3 ∨ (p2 ∨ p3))))))) → (((True ∧ p1) ∨ p4) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691415708611271108924372336304 : (((((False → p3) ∧ (True ∨ (True ∨ ((p4 ∧ p2) ∨ ((p5 ∨ p2) → (p2 ∨ p2)))))) → (p1 → (p3 ∧ ((p2 → (p4 → p1)) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302528183784659910110150427471 : (False ∨ (False ∨ (((p2 ∨ False) → p2) → (p3 ∨ (((True → p2) → p3) ∨ (True → (False ∨ (p2 ∨ (p5 ∨ ((p4 ∨ False) ∨ (False ∨ True))))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223953235294242295041848633270 : ((p4 ∨ (False ∨ True)) ∧ ((p3 ∧ ((((p1 → ((p5 ∧ p1) → p4)) ∨ p4) → p4) ∧ (p4 ∨ p2))) ∨ ((((False → p5) ∧ p2) ∧ p4) → p4))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315029168998179525450657689251 : (p3 ∨ ((False ∨ (p5 ∧ ((p2 ∧ (True ∨ False)) ∨ True))) ∨ (((((p1 → (p3 → False)) ∧ (p3 ∧ True)) ∨ (p3 ∨ True)) ∨ (p3 ∨ p5)) ∨ False))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130188586224652095573179256277 : (((True → ((((((p1 ∨ (p3 → p2)) ∨ p1) ∨ ((p2 ∨ p4) ∧ p3)) ∨ (False ∨ p2)) ∧ True) → p1)) ∨ (p3 → p3)) ∧ (False ∨ (p4 → p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141403667909409464347973721719 : (((False ∧ (True ∧ (p4 ∨ p1))) → ((p3 ∧ False) → (((((True ∨ (False ∨ (False ∨ p3))) → p5) ∨ p3) → True) ∧ p1))) → (p1 ∨ (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185077836021831148933744277455 : (((False ∨ False) ∨ ((True ∧ ((p5 → (p3 ∧ p3)) → p5)) ∧ False)) ∨ ((((((p3 → p1) ∨ p4) ∨ p3) ∧ ((False ∧ p5) ∧ p4)) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315649995944572467603852993769 : (p3 ∨ ((p1 ∧ p1) ∨ (((p2 ∨ p4) ∨ (True ∧ (p4 ∧ True))) ∨ ((((p2 ∨ True) ∨ p5) → p5) ∨ ((p5 ∨ p2) → ((p1 ∧ False) → True)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337878207265135869674896862778 : (p1 → (((((p4 ∨ True) ∧ (p1 → (((p2 ∧ False) ∧ True) ∧ p1))) ∧ p1) ∧ p5) → (((p2 → (p4 → (True ∧ p3))) ∨ p2) → (p3 ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h12 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h13 := h10 h12
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- We need to get the left conjuct of h14 based on <expert-advice>.
      let h15 := h14.left
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h18 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h19 := h10 h18
      -- We need to get the left conjuct of h19 based on <expert-advice>.
      let h20 := h19.left
      -- We need to get the left conjuct of h20 based on <expert-advice>.
      let h21 := h20.left
      -- We need to get the right conjuct of h21 based on <expert-advice>.
      let h22 := h21.right
      -- False on the left can always be used.
      apply False.elim h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h2.left
    let h25 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h24.left
    let h27 := h24.right
    -- Conjunctions on the left can always be decomposed.
    let h28 := h26.left
    let h29 := h26.right
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h30 =>
      -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
      have h31 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h29, we can now drive its conclusion.
      let h32 := h29 h31
      -- We need to get the left conjuct of h32 based on <expert-advice>.
      let h33 := h32.left
      -- We need to get the left conjuct of h33 based on <expert-advice>.
      let h34 := h33.left
      -- We need to get the right conjuct of h34 based on <expert-advice>.
      let h35 := h34.right
      -- False on the left can always be used.
      apply False.elim h35
    case inr h36 =>
      -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
      have h37 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h29, we can now drive its conclusion.
      let h38 := h29 h37
      -- We need to get the left conjuct of h38 based on <expert-advice>.
      let h39 := h38.left
      -- We need to get the left conjuct of h39 based on <expert-advice>.
      let h40 := h39.left
      -- We need to get the right conjuct of h40 based on <expert-advice>.
      let h41 := h40.right
      -- False on the left can always be used.
      apply False.elim h41
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h42 =>
    -- Conjunctions on the left can always be decomposed.
    let h43 := h2.left
    let h44 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h45 := h43.left
    let h46 := h43.right
    -- Conjunctions on the left can always be decomposed.
    let h47 := h45.left
    let h48 := h45.right
    -- Disjunctions on the left can always be decomposed.
    cases h47
    case inl h49 =>
      -- We want to use the implication h48 based on <expert-advice>. So we show its premise.
      have h50 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h48, we can now drive its conclusion.
      let h51 := h48 h50
      -- We need to get the left conjuct of h51 based on <expert-advice>.
      let h52 := h51.left
      -- We need to get the left conjuct of h52 based on <expert-advice>.
      let h53 := h52.left
      -- We need to get the right conjuct of h53 based on <expert-advice>.
      let h54 := h53.right
      -- False on the left can always be used.
      apply False.elim h54
    case inr h55 =>
      -- We want to use the implication h48 based on <expert-advice>. So we show its premise.
      have h56 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h48, we can now drive its conclusion.
      let h57 := h48 h56
      -- We need to get the left conjuct of h57 based on <expert-advice>.
      let h58 := h57.left
      -- We need to get the left conjuct of h58 based on <expert-advice>.
      let h59 := h58.left
      -- We need to get the right conjuct of h59 based on <expert-advice>.
      let h60 := h59.right
      -- False on the left can always be used.
      apply False.elim h60
  case inr h61 =>
    -- Conjunctions on the left can always be decomposed.
    let h62 := h2.left
    let h63 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h64 := h62.left
    let h65 := h62.right
    -- Conjunctions on the left can always be decomposed.
    let h66 := h64.left
    let h67 := h64.right
    -- Disjunctions on the left can always be decomposed.
    cases h66
    case inl h68 =>
      -- We want to use the implication h67 based on <expert-advice>. So we show its premise.
      have h69 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h67, we can now drive its conclusion.
      let h70 := h67 h69
      -- We need to get the left conjuct of h70 based on <expert-advice>.
      let h71 := h70.left
      -- We need to get the left conjuct of h71 based on <expert-advice>.
      let h72 := h71.left
      -- We need to get the right conjuct of h72 based on <expert-advice>.
      let h73 := h72.right
      -- False on the left can always be used.
      apply False.elim h73
    case inr h74 =>
      -- We want to use the implication h67 based on <expert-advice>. So we show its premise.
      have h75 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h67, we can now drive its conclusion.
      let h76 := h67 h75
      -- We need to get the left conjuct of h76 based on <expert-advice>.
      let h77 := h76.left
      -- We need to get the left conjuct of h77 based on <expert-advice>.
      let h78 := h77.left
      -- We need to get the right conjuct of h78 based on <expert-advice>.
      let h79 := h78.right
      -- False on the left can always be used.
      apply False.elim h79



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111873373215347906709362587542 : ((((p2 ∨ ((True ∧ ((True → ((p3 → p5) ∧ p3)) → p3)) ∧ ((p1 ∧ True) ∨ p5))) ∨ (((p4 ∨ p3) ∨ p3) ∧ True)) ∨ p2) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172033829893673240704719500731 : (((p4 ∧ (((((p1 → (p1 → True)) → p1) ∧ p1) → p1) → p2)) ∨ (p4 → p2)) ∨ ((p2 → p5) → (((False → p3) ∨ True) ∨ (p1 ∧ p3)))) := by
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
theorem thm_5_vars_58885971009449903162613132927 : (((False ∧ p2) ∨ (((False ∧ p4) ∧ (((p4 → False) ∧ p2) → True)) ∨ (p4 ∨ (((p4 ∨ (p3 ∨ p2)) ∨ True) ∨ ((p4 ∧ p3) → p3))))) ∨ p3) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339736114028897572087712388550 : (p1 → (p4 ∨ ((((p1 ∨ (p5 → (p5 ∨ (p5 ∧ True)))) → False) ∨ (p1 → (p5 ∧ ((False → p2) ∧ (False ∨ (p3 ∧ p2)))))) ∨ (False → p2)))) := by
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
theorem thm_5_vars_328609372314898495212730298223 : (True → (((((p3 ∨ p4) → (p4 ∧ True)) ∧ (p5 ∨ (p3 ∨ (p5 ∨ False)))) → p3) ∨ ((((False ∨ p5) ∧ p2) → p1) → (True ∨ (False ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53706127396667431482817168113 : (((p1 ∨ (((True ∨ p4) ∧ ((p2 ∨ False) ∧ False)) ∨ True)) ∧ (((p5 → p4) ∨ (((p4 ∨ p1) → (True ∨ True)) → (p5 → p2))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25353826845675031509249985625 : ((((p5 ∧ p1) → p5) → (((p3 ∧ p5) ∨ (((p2 ∨ (((((p4 ∨ p5) → p2) → (p4 ∨ True)) ∨ p4) → True)) → p5) ∧ p4)) → p5)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : (p2 ∨ (((((p4 ∨ p5) → p2) → (p4 ∨ True)) ∨ p4) → True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h11 := h7 h9
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766064374055975692357059432606 : (((p4 ∧ ((p1 ∨ (p3 ∨ False)) ∨ ((((((True ∧ ((False ∧ p4) ∧ True)) ∧ (p3 → False)) ∨ True) ∨ p2) → (p3 ∧ True)) ∨ (True → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642079016337088890009534437003 : ((((True ∧ (((False ∧ p4) → ((True → p5) ∧ (((False → ((p3 ∧ p2) ∧ False)) ∨ (p3 → False)) ∧ (p5 ∧ p4)))) ∨ (True → p5))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179228044451369919123987391558 : ((p4 ∧ (False ∨ (((p5 ∨ p1) → (p5 ∧ ((p5 → False) ∨ p2))) ∨ p5))) ∨ (True ∧ (p3 ∨ (((p2 → True) → ((False ∨ p3) ∧ p2)) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



