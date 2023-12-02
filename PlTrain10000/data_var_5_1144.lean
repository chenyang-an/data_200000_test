variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157105704384503488379150522065 : (((p3 → ((((True ∨ True) ∧ (False ∨ p1)) ∧ False) ∨ (((False → True) → (p1 ∧ True)) ∨ p4))) ∨ p3) ∨ ((True ∧ ((p2 ∧ p4) ∧ p4)) → p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216985821253396411217012094747 : (((p4 → (p2 ∨ p3)) ∧ p5) → ((p4 ∨ ((p4 → (p2 ∧ (p1 → p2))) ∨ ((False → False) ∨ p5))) ∧ (((False → p1) ∨ (p3 → p4)) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40546279138580512250219162079 : ((((p5 ∨ (p4 ∧ (p5 ∨ (p1 ∨ (p1 ∨ ((((p4 → p4) ∧ False) ∨ p2) → (((p3 ∨ (p4 ∨ p3)) ∨ p4) ∧ p1))))))) ∨ True) ∨ p1) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190661972476762628479918609810 : (((p5 ∨ (p4 → (p1 → ((False ∧ p1) ∧ True)))) → False) ∨ ((True ∨ True) → (True ∨ (((p5 → (True ∧ p3)) ∧ (p4 → p2)) → (p2 ∨ p4))))) := by
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
theorem thm_5_vars_203906872830774803996401315738 : ((p1 → (p4 ∨ ((False ∨ True) ∨ p1))) ∧ (False ∨ (((p3 ∧ ((p2 ∧ ((p4 → (p3 ∧ p3)) ∨ True)) ∧ p3)) ∧ False) ∨ ((True ∨ p4) → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118454866162833032602859315644 : ((p3 ∨ (((((p1 ∨ p1) ∧ ((True ∧ p1) ∨ False)) ∨ ((((True ∨ (False ∧ (p3 ∧ p2))) → p5) ∧ p4) ∧ p4)) ∨ True) ∨ p4)) ∨ (p4 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247435370594804697286596509731 : ((False ∨ p2) ∨ ((((p3 ∨ p3) ∨ True) ∧ p1) ∨ (True ∨ ((p2 ∨ p4) → (False → (p4 ∧ ((p4 ∨ ((True ∧ False) ∧ (False → p4))) → p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347111750064090560582853545266 : (p3 → (((p5 → (p4 ∧ p5)) ∨ (p2 ∨ ((False → (p5 → (p1 ∨ False))) ∧ p1))) ∨ ((p5 ∨ ((p1 → (p4 ∧ False)) ∨ False)) ∨ (p1 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63394649433867511995266077970 : ((p5 ∧ (p2 ∨ (((((False ∨ (True ∧ True)) → (p1 ∧ False)) → ((True → False) ∧ p1)) ∧ ((p1 ∧ False) ∨ (p2 → (p1 → p4)))) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311948820650475434094900808879 : (p2 ∨ (p3 ∨ ((((p5 → p2) ∨ (p5 ∨ (p3 ∨ p2))) → (p3 ∧ p5)) ∨ (((((True ∧ p1) ∧ p1) → p1) ∨ (True ∧ False)) ∨ (p5 → False))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327050757707411815932073594928 : (True → ((((True ∧ ((False ∨ p3) ∧ p2)) ∧ p3) ∧ (False ∧ ((p4 → p2) → (((((p4 ∨ p1) → (p4 ∨ True)) ∧ p1) ∨ p1) ∧ p2)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171790914396738760090121880971 : ((((((p4 ∧ p5) ∨ ((False → p1) ∨ p1)) → (p4 ∧ p4)) → (p5 → p1)) → p3) ∨ ((p1 → ((((p1 → True) → p3) → True) ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645257318162991958159476747965 : ((((p3 ∨ (p2 ∨ ((((p2 ∨ (p1 → p2)) → ((p4 ∨ p5) → True)) ∨ p5) ∧ (((p3 ∧ p4) → p3) ∨ ((True → p3) → p4))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642668176363660358566695333776 : ((((p1 ∧ ((p3 ∨ (((p2 ∨ True) ∧ p2) → ((p1 ∨ True) ∨ (p2 ∨ (p3 → p2))))) → ((p1 ∧ ((p5 ∨ p3) ∨ p4)) ∧ p3))) → p3) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p3 ∨ (((p2 ∨ True) ∧ p2) → ((p1 ∨ True) ∨ (p2 ∨ (p3 → p2))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h4
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- One of the premise coincides with the conclusion.
  exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799276357519025171029224123668 : (((p1 → (p3 ∧ (p3 ∨ ((((p5 ∧ (p1 ∧ p3)) ∧ (p3 ∨ (True ∧ (False ∨ (True ∧ (True ∧ (p4 → p5))))))) ∧ p2) ∨ (p1 → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234002097737050672291796758945 : ((p5 ∨ (p2 ∨ True)) → (p4 ∨ (((p3 → p4) ∧ ((p5 → p3) → p5)) ∨ ((p1 ∨ (((p4 ∧ (p3 → True)) ∧ p5) → (False → p2))) → True)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119479702649561621778906338644 : ((p4 → (p3 ∧ (True → (False ∨ (p5 ∨ (((((p5 ∧ ((p1 ∨ ((p1 ∨ True) ∧ p4)) → False)) → p3) ∨ p4) ∧ p1) → False)))))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86024006834719273783280602776 : ((((False ∧ p3) ∨ ((True → (p4 ∧ p2)) ∧ (p2 ∧ p4))) ∧ ((p3 → (True → (p2 ∨ (p1 ∨ (p4 → False))))) ∧ (True ∨ (p4 ∨ p5)))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172958642942185297080304788612 : ((p4 ∧ (((((p4 ∨ (p2 ∨ p3)) ∧ (False → p2)) → False) → (p5 ∧ p1)) ∨ p3)) ∨ (True → (((p1 ∧ p4) → (p2 ∨ (True ∨ False))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327824423049574430969348497467 : (True → ((((p1 ∨ (((p5 ∧ ((p4 ∨ (p3 ∧ False)) ∨ False)) ∨ ((p3 → True) ∧ p3)) ∧ (p3 → p5))) ∨ True) ∨ (True ∨ p2)) ∨ (p4 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622577057217552282508201480032 : ((((p4 ∧ (((((True ∨ p3) ∧ p3) → p3) ∧ (p2 ∧ ((p5 ∨ p2) ∨ ((p5 ∧ (p1 ∨ ((p1 ∧ p5) ∨ False))) ∨ p3)))) ∨ True)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_788041508074875506927468473452 : (((p5 ∨ (((((p2 ∧ ((p2 ∧ ((p5 → (p3 → False)) → p2)) ∧ p4)) ∨ ((p5 ∨ False) ∨ (p3 ∨ True))) ∧ (p3 → p2)) ∨ p1) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201020815705124813118358160066 : ((p4 ∨ ((False ∧ (False → (p1 ∧ p4))) ∧ p3)) → (((p3 ∨ p5) ∧ (False → (p3 → p1))) → ((p5 → False) ∨ ((True ∧ p1) → (False ∨ p4))))) := by
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
    cases h1
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- False on the left can always be used.
      apply False.elim h13
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h21.left
      let h24 := h21.right
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192763154522559006445507223792 : (((p1 ∧ ((p2 → p5) ∨ (p5 → (p3 ∨ p2)))) → p4) → ((p5 ∧ p1) ∨ ((p4 ∨ p5) ∨ ((False → p4) ∨ (p4 ∨ (False ∨ (p3 ∨ p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327424759830013935763818340380 : (True → ((((False ∨ (((p1 → (True ∧ p2)) ∨ (False ∧ (False ∧ (p2 ∧ True)))) ∧ p3)) ∨ (p5 → p5)) → (True ∧ (p1 ∧ (p2 ∧ p5)))) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∨ (((p1 → (True ∧ p2)) ∨ (False ∧ (False ∧ (p2 ∧ True)))) ∧ p3)) ∨ (p5 → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232096182576240361054040259486 : (((p5 ∨ True) → False) → ((((((p3 → (p3 ∨ (((False → False) ∨ p5) → (p2 ∨ True)))) ∨ p5) ∧ False) ∧ p5) ∨ (p2 ∧ p4)) ∧ (True ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607012852504813261720504636373 : ((((((((p4 ∨ p3) → (p3 ∨ (p1 ∨ (p4 ∨ (True ∨ False))))) ∨ p2) ∧ (p3 → (((p1 → (p5 → p2)) ∧ True) ∨ p1))) ∧ False) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_190555991725929619984279038006 : (((((p4 ∨ (True ∧ p3)) ∨ p1) → (p2 ∨ True)) → p1) ∨ (False → (p3 → ((p4 → p5) ∨ ((True ∨ (p3 → (p5 ∨ (p5 ∨ True)))) → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232123347588955131219174275155 : (((p5 ∨ p4) → True) → (((((p5 ∧ ((p4 → (((False ∧ True) ∧ (p5 → False)) ∧ p1)) → (False ∧ p4))) ∨ True) ∨ (p3 → p3)) ∨ p3) ∨ p3)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135584144704044856808364282729 : ((((p3 ∧ (p5 ∧ ((p1 ∨ ((p3 ∨ p2) ∧ (False → (False → True)))) ∧ p5))) → p4) ∨ (((p3 ∨ p2) ∨ p2) ∨ p5)) ∨ (True ∨ (p4 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313006367270131399176450067265 : (p3 ∨ ((((p1 → (p5 ∧ (p5 → (((p1 ∨ p2) ∨ ((p4 ∨ p4) → p5)) ∧ (p2 ∨ p3))))) ∨ ((p3 → p2) → (True ∧ p5))) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158178270785894925837044822277 : ((((p1 ∨ False) → (p5 → p4)) → (p2 → (True → (((((False → p3) ∨ p5) ∧ False) ∨ True) → p3)))) ∨ ((False ∨ True) ∧ (False → (p1 ∨ p4)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232860025629507246526036560698 : ((p2 ∧ (p2 → True)) → ((p3 ∧ (p1 → ((((p5 ∧ p2) → False) → (True ∧ (p3 ∧ (p1 ∨ p5)))) → ((p5 → False) ∨ (True ∨ p2))))) ∨ p2)) := by
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
theorem thm_5_vars_305195063629816868846008052321 : (p1 ∨ ((p4 ∨ ((((p2 ∧ False) ∧ (p4 ∧ p4)) ∧ p3) ∨ (((p2 ∨ (False ∧ (p4 ∧ p4))) ∧ p1) ∨ p5))) ∨ ((True ∧ (False → p4)) ∨ p1))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158853838202113040389991410008 : ((False ∨ (((((((p3 ∧ p1) ∨ ((p5 ∧ p2) → True)) ∧ p5) ∧ p3) → False) ∧ (p5 ∨ p1)) ∧ p4)) ∨ ((p1 → (p4 ∧ True)) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114876566765445055604148589838 : (((((p1 ∧ p3) → p3) → (p2 ∧ (((p3 ∧ p2) → p1) ∨ (p5 ∨ False)))) ∨ (p4 ∨ ((False → p1) ∨ ((False ∧ False) → p1)))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621365130045389350183151250445 : ((((True ∧ (p1 ∧ ((((p4 → p2) → ((p1 → (False → (p2 ∨ ((p3 ∧ True) ∨ ((p3 ∧ p3) ∧ False))))) ∧ p4)) → False) ∧ p4))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_261288019731420457644249390088 : ((p5 → True) → ((p2 ∨ p2) ∨ ((p3 → (((p3 → True) ∨ True) → (p3 ∧ p5))) ∨ ((p5 → p1) ∨ (((p5 ∨ p1) → p3) ∨ (p1 → p1)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219874519539219537099968784968 : ((p3 → (p3 → (p4 ∧ p4))) → (((p2 → ((p5 ∧ ((p2 ∨ p3) → p2)) → p1)) ∨ True) ∨ ((True ∧ (p5 → p1)) → ((p3 ∨ True) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205063916901648476603403797271 : (((p2 → (p5 → (False ∨ True))) → p2) ∨ (p3 ∨ ((((True ∧ p3) ∧ (p5 → (p2 ∨ (p4 ∧ False)))) ∨ ((p4 ∧ p3) → (p3 ∨ False))) ∨ p1))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186083546976510333482712338554 : (((((p5 ∧ False) ∨ (True ∨ (p3 → (p2 → p5)))) → False) ∨ p1) → (((p2 ∧ ((False ∨ p5) ∧ p4)) ∨ p1) ∨ (p3 ∨ ((p4 ∧ p2) → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : ((p5 ∧ False) ∨ (True ∨ (p3 → (p2 → p5)))) := by
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
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149288788830866323150120802650 : (((p3 → p5) ∨ (((p4 ∨ ((False → p4) → p3)) → p3) ∨ (p5 ∨ ((p4 ∨ ((p4 ∧ p2) ∧ p1)) ∨ True)))) ∨ (p1 ∨ ((p5 ∨ p2) ∨ p1))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300392125039103574221112989936 : (False ∨ ((((p2 ∧ p1) → p5) ∨ (False ∨ (p4 ∧ ((((p2 ∨ p5) → (((p2 ∨ p3) ∨ p5) ∧ False)) ∧ True) → p4)))) ∨ (True ∧ (p5 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_764530730978096151131857891915 : (((p4 ∧ (((((p3 → False) ∧ ((p5 ∨ p3) ∧ (p1 ∧ ((((False → (False ∧ (p1 ∧ False))) → p5) → p1) ∨ p4)))) ∧ p2) → p3) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217639272209930180276869941911 : ((((p4 ∧ p1) → p4) → p2) → (((p1 ∧ True) → p3) ∨ ((p4 → p5) → (p3 → (True ∧ ((p5 → True) ∧ ((True ∨ True) → (p3 → p3)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115609579542039505126262319406 : (((p1 ∨ ((True → (p2 ∨ p1)) ∨ p1)) ∧ ((p1 ∧ True) ∧ (p2 → (((False ∨ (p5 ∨ p3)) → (p2 ∨ (p4 → p4))) ∧ p5)))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179136281354128457321634051646 : ((p1 ∧ ((p2 ∨ True) → ((((p5 → p1) → False) ∧ p5) ∧ (False ∨ True)))) ∨ (((p3 ∧ (p2 ∨ (p5 ∧ p1))) ∧ p5) → ((p4 ∧ p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623499467819555035239947358026 : ((((False ∨ (((p4 ∨ True) ∨ (p3 ∨ (p4 ∨ ((True → p2) ∨ p2)))) ∧ (((p1 ∨ p4) ∧ p3) ∨ (p1 → (False ∧ (p2 ∨ p2)))))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61188045547662857787565124061 : ((False ∧ ((p2 → True) ∧ (True → ((p5 → p3) ∨ (((p5 → True) ∨ (p4 ∨ (p5 → (p1 → (False ∧ (p1 ∧ (p5 → p4))))))) → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94665378086543187652990550677 : ((p3 ∧ ((((p5 ∨ (p5 ∨ (True → (p2 → p1)))) → False) ∧ (p4 → ((p2 → (True ∨ p5)) → ((True ∧ p5) → False)))) ∧ (p1 ∧ p3))) → p2) := by
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h10 : (p5 ∨ (p5 ∨ (True → (p2 → p1)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h13 := h6 h10
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65640100468666913727950516090 : ((p4 ∨ (((p4 ∧ (p2 ∨ (p3 ∧ (p3 ∧ (p1 → (p4 → True)))))) ∧ ((p2 ∧ (p5 → ((p4 ∧ (False → p5)) → p4))) ∧ p3)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166716296319824236341422475101 : ((p3 → (((p5 → p5) ∧ p5) ∧ (((False → False) ∧ (((p3 ∧ p5) ∨ p5) → p3)) → p1))) ∨ (p2 ∨ ((p2 → ((p1 ∨ True) ∧ False)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594096367950713617400051020807 : (((((((((True ∧ p2) ∧ p3) ∧ p3) ∨ ((p2 ∨ (False ∧ (p3 ∧ (p4 → p5)))) ∧ p2)) → p5) → ((p5 ∨ p3) ∧ (p1 ∨ p2))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56483266050943742396317649009 : (((True ∧ ((p2 ∨ True) → p4)) → ((((p3 ∧ ((((False ∨ p3) → p5) → p4) ∨ p5)) ∧ p5) → p1) → (((p3 → False) ∧ p3) ∨ True))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146401675886398133383325493518 : ((p2 ∨ (((p2 ∨ ((p4 ∧ (p2 ∨ (p1 ∨ p2))) ∨ ((p4 → (True → p2)) → p1))) ∧ p2) ∨ (False → p3))) ∧ (p5 → ((p4 ∧ p1) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40234293324632707924646164215 : ((((p2 ∧ (p3 ∨ ((False ∧ p5) ∨ ((False ∨ (p4 ∧ (p4 ∧ (((p1 → p2) ∧ p2) → p3)))) ∨ (p1 → (False → p3)))))) ∧ False) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206099962224465147660984453685 : ((p3 ∧ (p4 → (p3 ∧ (p1 ∧ p4)))) ∨ (((((p3 ∧ p1) ∧ p5) ∨ ((p3 ∨ p3) ∨ p3)) ∧ (p3 ∧ (p4 → (True ∧ True)))) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59349767467479806495206170156 : (((p5 ∨ p1) ∨ (((((((p5 ∧ False) ∧ p3) ∨ False) → p2) ∧ ((p2 → p5) ∨ ((p2 ∧ False) → (p3 → (p2 ∧ True))))) ∧ True) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640870754029942679112488667111 : (((((p4 → p2) ∧ ((p2 ∨ (((p4 → (False ∧ True)) ∨ p5) ∨ ((p1 → p4) ∧ p4))) ∧ (True ∨ ((False ∧ (p5 → p4)) ∨ True)))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330719846033917757412162130763 : (True → (p1 → (((((p3 → (((((p2 ∨ p4) → (True ∨ p3)) ∧ p1) → (False ∧ (True ∨ (p4 → p5)))) ∧ p2)) ∨ p2) ∧ p3) ∨ p2) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117822557268839722613404067642 : ((p4 ∧ (p1 ∧ ((p2 → ((p2 → (p4 ∨ ((True ∧ p5) → (p2 ∧ ((p1 ∨ p2) → p1))))) ∨ p3)) → (p5 ∨ (p2 → p5))))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750909606051501664188561178017 : (((True ∧ (((p5 → True) ∧ (((p2 ∧ p3) → p1) ∧ p1)) ∨ ((p2 ∧ True) → ((((False ∧ True) ∨ (False ∧ (p5 ∧ p5))) ∨ p4) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357269170078626463729092600558 : (p5 → ((p3 ∧ p2) ∨ ((p4 ∨ (((p4 ∧ (((p4 → (True ∨ False)) ∨ p5) → p1)) → p5) → ((p5 ∨ ((p3 ∨ p2) → True)) → p2))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65965218533058791304692694063 : ((p4 ∨ (p5 ∨ ((False ∨ p3) ∨ (p2 ∨ (((p1 ∧ ((p5 ∨ ((False → p5) → (True ∨ p4))) → p1)) → p1) ∧ ((p1 ∨ True) ∨ p3)))))) ∨ p3) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38141038704340817435576235591 : ((((p1 ∨ (p4 → (p5 ∨ (((((p1 → (p2 ∧ p4)) ∨ (p5 ∧ False)) ∨ p2) ∨ (p2 ∧ True)) ∧ p2)))) ∧ (p3 → (False ∨ p1))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153547442570079374602010128764 : ((True → ((p3 ∨ p1) ∧ (((p5 ∧ (p3 ∨ (p1 → ((p5 ∧ True) ∧ p4)))) → ((True → True) → p4)) ∧ p2))) → (True ∧ ((p2 → p5) ∨ True))) := by
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
theorem thm_5_vars_178624984269315981393877741918 : (((((p1 ∨ p1) ∨ (p3 ∨ p2)) → p4) → (True ∧ (p3 ∧ (False ∨ p3)))) ∨ ((False ∧ p3) → ((((p4 ∧ p4) → (p4 ∨ p2)) ∨ p1) ∧ False))) := by
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
theorem thm_5_vars_64790524705812835783507735792 : ((p2 ∨ (((p3 ∨ (((False ∧ False) ∨ ((p4 → p3) ∨ True)) ∧ p3)) → (True → ((p5 ∧ p5) ∨ (p1 ∨ (True ∨ (p4 ∧ p5)))))) ∨ p2)) ∨ p3) := by
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
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187372844185841711347801962043 : ((p3 ∧ ((p1 ∧ p2) → (p3 → ((p4 ∨ True) ∧ (p1 ∨ p5))))) → (p4 ∨ (((p3 → p2) → p4) ∨ ((p2 ∧ (p3 ∧ True)) → (p1 → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244356819058043143654397863397 : ((False ∧ False) ∨ (p4 ∨ ((((p1 → (p4 ∨ ((p2 ∨ False) ∧ True))) ∨ (False → p2)) ∨ True) ∨ (((p1 → (True → p3)) → (p4 ∨ p4)) ∧ p1)))) := by
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
theorem thm_5_vars_51860350620062830065426443239 : (((((((True → (p4 ∨ False)) ∨ (True → p4)) ∧ ((p5 ∧ p2) ∨ p3)) ∨ p2) ∨ True) ∨ ((False ∨ p2) ∨ (False ∨ (p5 → (p3 ∧ p5))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156967292094918102428511487771 : ((((p1 ∨ ((p5 ∧ (p4 ∨ ((p4 → p5) ∨ True))) ∧ p5)) ∧ (p5 ∧ (True → (False → p1)))) ∨ p3) ∨ (((False ∨ (True ∧ True)) ∧ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319632329721533889829020293796 : (p4 ∨ (((p4 ∧ ((p4 → False) ∧ (p5 ∨ p3))) ∨ p3) ∨ ((True ∧ (p3 ∧ ((p4 ∨ p3) → p1))) → (p1 → ((p3 ∨ p2) ∨ (False ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119135694283078237969079749301 : ((p1 → (p3 ∨ (((p2 ∧ (p2 ∧ ((p5 → p5) → ((False ∧ p5) → p5)))) → (p5 ∨ p3)) ∨ ((False → p4) ∨ (p1 ∧ p3))))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206792389154445755898771992966 : ((p4 → (p2 ∨ ((False ∧ False) ∨ p2))) ∨ (p2 ∨ (True ∨ ((((p5 ∨ p3) ∨ p5) ∧ ((p3 ∨ (p5 → False)) ∨ True)) ∧ ((p2 ∧ p2) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157734437709012619795800865776 : (((p1 → ((p2 → (p2 → True)) → (p3 ∨ (((p4 → p4) → p3) ∨ False)))) → ((p4 → False) → p3)) ∨ ((((True ∧ p2) ∨ p1) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205553451755057989372581612324 : (((p4 ∨ p2) ∧ (p5 → (False ∨ p5))) ∨ (((((p3 ∨ ((True ∨ False) ∧ p2)) ∧ (p4 → (p1 ∨ ((False ∨ p4) → p5)))) → p5) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740617932223758018193261450092 : ((((p2 ∨ p1) ∨ (False ∨ ((False ∨ (p2 ∨ p1)) ∧ ((p1 → ((p1 → ((p1 ∧ True) ∧ (False ∧ True))) ∧ p2)) ∨ (True ∧ (p5 ∧ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216533705366552728224496898561 : ((p5 → (p2 → (False ∨ p3))) ∨ (p2 ∨ (((p2 ∧ True) → (p3 → (p5 → (False ∨ (p1 → (p4 ∨ (True → ((p3 ∨ False) ∨ p4)))))))) ∨ p4))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186085394480121123210081228552 : ((((True ∧ (p4 → (((p2 ∨ p5) → p2) ∨ p5))) → p2) ∨ p5) → (False ∨ ((((p1 ∨ p1) ∨ p2) → ((True → p5) → p1)) ∨ (True → True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67323001064524050939434364747 : ((p1 → ((((p2 ∧ ((p2 → p2) ∨ ((p3 → False) ∨ p1))) → ((p2 → ((((p5 ∧ False) ∧ p5) ∧ p3) ∧ False)) ∨ True)) ∧ p4) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156817062220592206557198150281 : (((p3 ∨ ((((p4 ∧ False) ∧ (p5 ∨ ((((p4 ∨ p1) ∨ p3) → p5) → p3))) ∧ p5) ∧ p5)) ∧ p3) ∨ (True ∨ (p2 ∧ ((p5 → True) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759125413126968899397799483210 : (((p2 ∧ ((((p2 ∧ p1) ∨ True) → (False ∧ ((False ∨ p5) ∧ ((p3 ∨ ((((p5 ∧ p1) ∧ p5) ∨ p5) ∨ p1)) ∨ p2)))) ∧ (p5 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187313747787473486819711109024 : ((p1 ∧ ((p5 → p3) → ((p3 → ((p1 ∧ p5) ∧ p5)) ∨ p2))) → (p2 → (((True ∧ ((p3 → p5) ∨ False)) → p1) ∧ ((p3 → p4) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631671237134679208424412189686 : ((((((((False ∨ p2) ∧ ((True ∨ False) ∨ False)) ∧ ((True ∨ (p1 → True)) → p2)) ∨ (False ∧ (p2 ∨ (p1 → (True ∧ p4))))) → p4) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54357648070245445064386376101 : (((p3 ∨ (p4 ∧ (False ∨ (True ∨ (p3 ∨ True))))) ∧ ((p5 ∧ (p2 ∨ ((p2 ∧ p3) ∨ ((p4 ∧ (p3 ∨ p5)) → (p4 ∧ p4))))) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216754201673865738581676208844 : ((((p1 → p2) → p1) ∧ p3) → ((p2 → (p1 ∨ (p2 → (p4 ∧ (p5 → (True ∨ ((p5 ∧ (True ∨ True)) ∨ p1))))))) ∨ (True ∧ (p1 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320298446605782375863671512295 : (p4 ∨ ((p5 ∧ p5) ∨ ((p2 ∨ (p3 ∧ ((p5 ∧ True) ∧ (((True ∧ ((True ∨ p2) → (((False ∨ False) ∧ False) ∨ p2))) ∨ False) ∨ p3)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164741373602359915442771671281 : ((((((((p5 ∧ (False → p1)) ∨ (False ∧ p3)) → p3) ∨ p3) ∧ p4) ∨ (p2 ∨ False)) ∨ p2) ∨ (p5 → ((p1 ∧ (p2 ∧ p3)) ∨ (True → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115531587621005056689039754510 : (((p3 ∧ ((p1 ∧ p3) → (False → (p3 → p3)))) → (((True ∨ p5) ∧ (p4 ∧ (True ∨ (p2 ∨ (p2 ∨ (p3 → p4)))))) ∧ p2)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204036367620410706136563237828 : ((p4 → (True ∧ ((p1 ∨ p3) ∨ p4))) ∧ (((((((False ∨ p5) → True) → p4) ∨ p3) ∨ p3) ∨ (p1 ∨ False)) ∨ ((p4 ∧ False) → (p3 ∨ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
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
theorem thm_5_vars_111079912906071236630906862433 : (((((p2 ∧ (p3 → (p1 ∧ ((p5 ∧ p4) ∧ (p2 → p2))))) ∧ p1) ∧ (p2 ∧ (((p1 ∨ False) → (p2 → p4)) → p2))) ∧ p1) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337099515816611847533023639194 : (p1 → (((((False → p4) ∧ (p3 ∨ False)) → p1) → (False ∧ (((p5 ∨ (False ∨ (p1 → ((p5 ∧ p4) ∧ p4)))) ∨ p2) ∧ True))) ∨ (p1 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64383892006191727833182327757 : ((p1 ∨ ((p4 → (((False ∧ ((p3 ∧ True) → (p5 → (True ∨ p5)))) → False) → ((p2 → ((p4 ∧ (p4 → p5)) ∨ p1)) ∧ p3))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58907968822226595758703374978 : (((p1 ∧ True) ∨ ((False → (False → (p3 → ((p5 ∧ p4) ∧ ((False ∧ p2) → ((p1 → p4) → p5)))))) → ((p4 ∨ True) ∧ (p4 → p4)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_427762454106622363859675887349 : ((((((((p2 ∨ p4) ∨ (p3 ∨ p2)) ∨ ((p5 → (p5 ∨ p4)) ∨ (p4 → ((False → p4) → p5)))) → (p4 ∧ p3)) ∨ True) ∨ (p3 → False)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227619334381706111211023747100 : ((False ∧ (p1 ∨ True)) ∨ (((p4 ∨ (p5 ∨ (p1 → (p2 ∨ (True ∨ p5))))) → (((p4 → True) → p2) ∧ (((p2 ∨ p3) → p5) ∧ p2))) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ (p5 ∨ (p1 → (p2 ∨ (True ∨ p5))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792223096724745915392195001963 : (((True → ((((p4 → True) ∨ True) → ((p2 → (True → (p4 → (((p2 ∨ True) ∨ p5) → p1)))) ∧ False)) ∨ (False ∨ (p3 → (p2 ∨ p3))))) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116497430378109883341183441868 : (((p3 ∧ p1) ∧ (p3 ∧ (((p1 ∨ p2) ∨ (p2 → ((p1 ∨ (True → p4)) ∨ p5))) ∧ ((p4 ∨ (p2 ∨ (True → False))) ∨ False)))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591633731218139783837545435477 : (((((((((p4 → p1) → (False ∨ ((p5 → p4) → (p1 ∨ True)))) ∨ False) → (p5 ∨ ((p2 ∨ p1) ∧ True))) ∧ p5) ∨ (p3 → True)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



