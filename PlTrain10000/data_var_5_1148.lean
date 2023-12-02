variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117470878360034298096616153573 : ((p1 ∧ (p3 ∧ (((p3 ∧ (((p4 → (True ∨ p4)) ∨ True) → p4)) ∧ (True ∧ (False ∧ ((False ∧ (p2 ∨ True)) ∧ p1)))) ∧ p3))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58127463103655786254909630912 : (((p2 ∧ False) ∧ (((p5 → p4) → p2) → (((p3 ∧ (((p4 ∨ False) ∨ (((p4 ∧ p3) ∧ (p3 → p2)) → p1)) → p4)) ∨ p5) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51931874679664341983846719694 : (((((((p2 → p4) ∨ p5) ∧ True) ∨ ((p1 ∨ p4) → p2)) → ((False ∧ False) ∨ p4)) ∨ ((p4 ∧ (p2 ∨ ((True ∨ False) ∨ p4))) → p4)) ∨ p3) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h8
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40615985906624498893317875213 : ((((((True → True) ∨ (((p1 ∨ p2) → (((p1 ∧ p4) ∧ ((False ∨ (p4 → p3)) ∨ p3)) → p2)) → (p5 ∨ True))) ∨ p4) → False) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42179768191225022943490861011 : (((True ∧ (((p1 → (p1 ∨ ((p1 ∧ p5) ∧ (p2 ∧ ((False → True) ∧ (p1 → p2)))))) ∨ ((p2 ∧ p5) ∧ (False → p3))) → p5)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66845959439375016867321527933 : ((True → (p4 → (((((p4 ∧ p2) ∨ (p1 ∧ (p3 ∨ p3))) ∧ ((p4 ∨ (p4 ∧ ((p1 ∧ (p5 → p4)) → True))) → p5)) ∨ p3) ∨ True))) ∨ p4) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114498768926929889266022147882 : (((((p5 → (p4 ∨ p3)) → (False ∧ True)) → ((p5 ∧ (p5 ∧ (True → (True ∧ p1)))) ∧ p5)) → (((p3 ∧ False) ∨ p1) ∨ True)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224813610339052249958057542830 : ((p4 → (True → True)) ∧ ((((p5 ∧ True) ∧ False) ∧ (False ∨ (p2 ∨ (p3 ∧ p3)))) ∨ (((p5 ∧ p1) ∨ p1) → ((p2 ∧ p5) ∨ (p2 → True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181610117958862766618741653417 : ((p2 → (((False ∧ (p2 ∨ ((p5 → p3) ∨ p1))) ∧ (p2 ∨ p2)) → p4)) → (((p4 ∨ p4) ∧ ((p3 ∧ (p3 ∧ (p2 ∧ p1))) ∧ True)) → p3)) := by
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
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h4.left
    let h16 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185042745747919491872242140671 : (((p3 → True) ∧ (p5 ∨ (True ∧ ((p4 ∨ p5) ∧ (p2 ∧ p2))))) ∨ (False → ((((((False ∧ p1) ∨ p4) ∧ False) ∧ p3) ∧ True) → (False → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134880884793421236766150320090 : (((p3 → ((((p5 ∧ p4) → (p5 ∨ True)) ∨ ((p2 → (((True ∨ p5) ∨ p5) ∧ True)) ∨ (p1 → p1))) ∨ False)) → False) ∨ ((False ∧ p4) → p1)) := by
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
theorem thm_5_vars_50461652804970154909153164708 : (((p5 ∨ (((p5 ∧ p5) ∧ (((p5 ∨ (p2 ∧ False)) ∧ ((False ∧ p5) ∨ p3)) ∨ p3)) ∨ (p4 ∧ p3))) ∨ (p2 → ((p1 ∧ p3) → p3))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_309606546259614250464434974697 : (p2 ∨ ((((((p3 ∧ ((((p3 → True) ∨ (p3 → p4)) ∨ p2) ∨ p5)) ∧ True) ∨ p3) → (p1 ∨ (False ∨ True))) ∨ p1) ∨ ((False ∨ p3) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106517951743585630201382929779 : ((((True → ((True ∧ p5) ∨ p3)) → (p4 ∨ p1)) ∨ ((True ∨ p2) ∧ (p1 → (p5 ∨ ((p3 → ((True → True) ∨ p3)) ∧ p1))))) ∧ (p5 → p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54962061811725109741995149381 : ((((False → (False ∧ p1)) ∨ (p5 → True)) ∧ ((((p4 ∨ (p3 → (p1 ∧ p2))) → (p2 → p5)) ∧ p4) ∨ (((p3 → p5) ∨ p1) → True))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129077303183456149449373532576 : ((((((p3 → (((p1 ∧ True) → p4) ∨ p5)) → (p1 ∨ p2)) ∨ ((True ∧ (p4 ∧ (p2 ∨ p5))) ∧ p4)) ∨ p1) ∨ True) ∧ (False ∨ (p4 → True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67520846919978101885365434057 : ((p1 → (((p1 → ((True → p1) ∧ p3)) ∨ p4) → (True → (((p5 ∨ ((p2 ∧ True) ∨ p4)) ∨ (True → (p3 → True))) ∨ (False ∧ p1))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111897671374313872099895641595 : ((((p4 ∨ ((((p3 ∨ p4) ∧ (False ∨ p1)) → p3) → ((p2 ∨ p5) ∨ p2))) ∨ (p1 → ((True ∨ p4) ∨ (p4 ∨ p3)))) ∨ p1) ∨ (False ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655596301349560485468177419278 : ((((((p5 → p3) → (False → ((((False → (p1 ∨ p5)) ∨ (p1 → p2)) → False) ∨ ((p1 ∧ p5) ∧ p2)))) → (True ∧ False)) ∨ (p4 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156998763108401759646278322352 : ((((p2 ∧ ((True ∧ p3) ∧ p3)) ∨ (((p5 ∨ (p4 ∨ ((p4 ∨ True) → p1))) ∨ p5) ∧ p2)) ∨ p4) ∨ (p2 ∨ ((False → (p3 → p4)) ∨ p3))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259941418207037081105278709664 : ((p1 → p5) → ((((p3 → (True → (p3 → p2))) → p3) ∨ (p4 ∧ False)) ∨ ((p1 ∨ (p3 ∧ p5)) ∨ (((True → (p1 ∨ True)) → p1) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True → (p1 ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53160566519206448454637786140 : ((((p2 ∧ (((p5 → p5) ∧ ((p3 ∧ p3) → p1)) → p2)) ∨ p5) ∨ ((True ∧ p3) ∧ (((True → p5) ∧ (p3 ∧ (p2 ∨ p3))) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720082543665559485630749189205 : ((((((p2 ∨ p4) → p1) ∧ p2) → (((True → (p5 ∧ ((p1 ∨ (p5 ∨ (True ∧ p1))) ∧ (p2 → True)))) ∨ ((p4 ∧ p2) ∨ p4)) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636998192105989381091186688688 : (((((((p3 ∨ True) ∨ p4) ∧ (((True ∨ (True ∨ p5)) ∨ True) ∧ p5)) ∧ (p1 ∧ (((((False ∧ False) ∧ True) ∨ p2) ∨ True) ∨ True))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129210254244325179484293723613 : ((((((p5 ∨ (p3 ∧ p3)) → (False ∨ ((p2 ∨ p5) ∨ p3))) ∨ (True ∨ p3)) ∨ ((p5 ∧ (True → p1)) ∨ True)) ∨ p5) ∧ (True ∨ (p5 ∨ p1))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191558181622708137620980530306 : ((p1 ∧ (p2 ∨ ((p2 → (p2 ∨ (p3 ∧ p4))) → p1))) ∨ (True ∨ (((p5 ∧ (p3 → p2)) ∨ ((p5 ∧ p3) ∧ (p5 ∧ (p1 ∧ False)))) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156869513042925061762254952161 : (((((p1 ∧ True) ∨ (((True → p2) ∨ ((p5 ∧ p3) ∧ (p3 ∨ (p1 ∧ p4)))) ∨ p3)) ∧ p2) ∨ p1) ∨ (p5 ∨ (p3 → (p4 → (p2 ∨ p3))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193068190520096408112240662006 : ((((p2 ∧ (p2 ∨ p5)) ∨ False) ∧ (p2 ∧ (p4 ∨ p5))) → (((p1 → False) ∨ p2) → (((p3 ∨ p5) ∧ p4) ∨ (p2 ∨ (True ∨ (True ∨ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h5.left
        let h11 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h5.left
        let h16 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h15
    case inr h19 =>
      -- False on the left can always be used.
      apply False.elim h19
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h1.left
    let h22 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- Conjunctions on the left can always be decomposed.
        let h27 := h22.left
        let h28 := h22.right
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h29 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h27
        case inr h30 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h27
      case inr h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h22.left
        let h33 := h22.right
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h32
        case inr h35 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h32
    case inr h36 =>
      -- False on the left can always be used.
      apply False.elim h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90248193204695007473406820529 : (((p2 ∨ (False → True)) → (((False → p5) ∧ ((p1 → p2) ∨ (((p4 ∨ (True ∨ True)) ∧ p3) → True))) ∧ ((p2 ∧ (p4 ∧ True)) ∧ True))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ (False → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158594124152898356449005294095 : ((False ∧ ((p1 ∨ ((p5 ∨ (p4 → (p4 ∧ (((p5 ∧ (p4 ∨ p5)) ∧ False) → p3)))) ∧ p5)) ∧ p4)) ∨ (p1 → (p1 ∨ ((p5 ∧ False) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43273515868113091216993425277 : ((((((((((((p4 ∨ p2) ∧ ((p1 ∨ p4) ∨ p3)) ∧ False) ∧ p2) ∨ p5) ∨ (True ∨ (True ∨ p4))) → True) ∧ p3) ∧ p4) ∨ True) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308630066579110057711186590994 : (p2 ∨ (((p5 ∨ True) → ((False → (False ∧ (p4 ∧ (p5 → (True → (True → (p3 ∧ p5))))))) ∧ ((p3 ∨ (p2 ∧ (p1 ∨ p5))) ∨ True))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319396419084005928896186809982 : (p4 ∨ (((p1 ∧ (((p5 → True) ∨ ((p4 ∧ True) → p4)) ∨ False)) ∨ (True → False)) → ((p4 ∨ p5) ∨ ((p2 → ((p5 ∨ p1) ∧ p1)) → p1)))) := by
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
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113206573888280732497338298122 : (((((((True ∨ (p4 → ((True ∧ p4) ∧ (p2 ∧ False)))) → p1) ∨ p1) ∧ (p3 ∨ ((True ∧ True) → False))) ∨ p1) ∧ (False ∨ False)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175143122833419989341710334942 : ((p5 ∧ ((False ∨ ((p2 → False) ∧ p5)) → ((p1 → False) → ((p3 → p5) ∧ p4)))) → (p3 → ((True ∧ (((p4 ∨ True) → True) → p2)) ∨ True))) := by
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
theorem thm_5_vars_49438094687255660471226881234 : (((((True ∧ (((p1 → (((p2 → (p4 ∧ True)) ∧ p4) ∨ True)) ∨ p1) ∨ (p4 → p5))) → (True → True)) ∨ p5) → ((p1 ∧ p5) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_206334486196495295278155635458 : ((p1 ∨ (p5 → (p4 ∧ (p3 ∨ p3)))) ∨ (((p3 ∧ (True ∧ p4)) → ((p2 ∨ (p2 ∧ True)) ∨ (p4 ∧ (True ∨ p5)))) ∧ ((p5 ∧ p2) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179380843280033310400034462266 : ((p3 ∨ (((p4 ∧ (p2 ∨ ((p2 → p3) ∨ p5))) ∧ (p1 ∨ p2)) ∧ True)) ∨ (p5 ∨ ((False → p4) ∨ (p5 → (((False → False) ∨ p3) → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164925067642223206807372670647 : ((((((p4 → p3) ∨ (False ∧ (((p1 → False) → p2) → p5))) ∨ (p2 → p2)) ∨ p5) → False) ∨ ((p5 → True) → ((p4 → (p3 ∧ p1)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317616821290427372822584124034 : (p4 ∨ ((((((((False ∨ p5) → True) ∧ ((p3 ∨ False) ∨ (p4 ∨ ((False → p2) → False)))) ∨ ((True ∧ p2) ∧ p5)) ∨ False) ∨ p2) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743628787014941433233792412857 : ((((True ∧ p1) → ((p2 ∧ (((False ∨ (((p5 → False) → (p5 → p4)) ∨ ((False → p1) → p4))) → p3) ∨ (True → p3))) ∨ (True → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115368724806891632194987361535 : ((((p3 ∧ (True ∨ ((False ∨ p3) → p1))) → p4) ∧ (((True → (p4 → (True ∨ (((p1 → p3) → True) ∨ p1)))) → False) ∨ p1)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326328002796496597058639273739 : (p5 ∨ (p4 → (True → ((p3 ∨ ((p5 → p5) ∧ ((p5 → (((False ∧ False) ∨ (p2 → (((p3 ∨ p5) → p1) ∧ False))) ∨ p1)) ∨ p4))) ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611960939088702724675354126171 : (((((((p4 ∧ (((True ∨ p3) ∨ (p2 → False)) → (p2 → (((p5 ∨ p1) → (p4 ∨ p1)) ∨ p4)))) ∨ False) ∨ False) ∧ (p4 ∧ p5)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184498173498013409497979663293 : (((((p5 → p1) → p2) ∨ ((p3 ∨ p5) ∧ p4)) ∨ (p5 → p4)) ∨ (((p3 ∨ p1) ∨ (False → p3)) ∨ ((True ∨ (p3 ∨ (p3 ∨ p3))) ∧ p5))) := by
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
theorem thm_5_vars_228495685948516404494330402421 : ((False ∨ (p2 → p5)) ∨ ((False ∨ (False ∨ ((((p1 ∧ True) ∧ (p3 → (p5 → False))) → (False ∨ ((p3 ∧ p1) ∧ (p4 ∧ False)))) ∧ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194110150577283769213714102579 : ((False → (((p1 ∧ p5) ∧ True) ∧ ((p2 ∨ p4) ∨ p2))) → (p2 ∨ ((((p3 ∧ p1) → True) → ((p5 → p4) → (p5 → (False ∨ p5)))) ∨ False))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20210318740525466852998481762 : ((((((p3 ∧ True) ∧ (False ∧ p3)) ∧ ((True → p1) → p3)) ∨ (p5 ∧ p2)) ∨ (((p2 → p5) → False) → (((False → False) ∧ p5) → p2))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p2 → p5) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116156702651131914800909491891 : (((p3 ∨ (p2 ∧ p2)) ∧ ((p1 ∧ ((p3 ∨ False) ∧ (((p1 → p5) ∧ True) ∨ ((True ∧ ((p3 ∧ p2) ∨ p1)) → p5)))) → p2)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257999573666507793640021179531 : ((p4 ∨ p1) → ((p5 ∧ ((p3 ∧ False) ∨ ((False ∨ False) ∨ p1))) ∨ (True → ((p3 → (p1 ∨ ((p1 ∨ (p2 → True)) ∧ (p3 ∨ p2)))) → True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53620450771978953585406104113 : ((((False ∧ (p4 → (p2 ∨ (False ∧ False)))) → (p5 ∧ p3)) ∧ (((p4 ∨ (p1 ∨ p4)) ∨ p5) ∧ ((p4 ∨ (p5 ∧ p4)) ∧ (p3 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668809088333757426589579405472 : ((((((((p5 ∧ p4) ∧ (p1 ∧ p1)) → (((True → p4) → True) → False)) ∧ ((p1 → p4) → (False ∨ p5))) ∨ True) ∨ (p3 → (p3 → p5))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42382740630667600423762968500 : (((p4 ∧ (((False → (p4 → True)) → ((p1 ∨ p2) ∨ (p2 ∧ ((False ∨ (p1 ∧ p2)) ∧ (p5 → p2))))) ∨ ((p2 ∨ p2) → p2))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57646193966779763120254857213 : ((((False ∨ p3) ∨ p2) → (((p5 → p5) → (True ∧ ((p1 → ((p5 ∧ (p1 ∨ p5)) → p2)) → p4))) ∨ (((p2 ∨ p3) ∨ p5) ∨ True))) ∨ p2) := by
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
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137735483289841783541719054960 : ((p1 ∨ (p5 ∨ ((((p3 → p5) ∨ False) ∧ (p1 ∧ (p4 ∨ p4))) → ((p2 ∨ (p3 ∨ p5)) → ((p2 ∨ p3) ∨ p2))))) ∨ (True ∨ (p3 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330598868759265219659541800658 : (True → (True → (((p1 → (((p5 ∧ False) → (p3 ∧ (((((p2 → ((p3 → False) → False)) ∧ p1) ∧ False) ∧ p4) → True))) → p2)) ∨ p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134178183247839411847687534370 : ((((False → ((((False → (p1 ∨ False)) ∧ True) → p4) ∨ ((p5 → p2) ∧ p2))) → (False ∧ ((p1 → p1) ∨ True))) ∨ p5) ∨ (p5 ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118119057536934578183974803532 : ((False ∨ ((True ∨ ((((False ∨ p2) ∨ p2) ∨ ((p4 → (p5 → p1)) ∨ p5)) → (p1 ∧ (False → (False ∧ (p1 → False)))))) → p3)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179529267571613239963015653865 : ((p1 → ((((p2 ∧ True) ∨ ((p1 → (p1 → p5)) → p3)) ∧ p2) ∨ False)) ∨ ((p5 ∧ ((p5 ∧ ((p3 ∧ p2) ∨ (p5 ∧ p2))) ∨ p5)) → p5)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675300022985852600441717359020 : ((((((((((((p5 → p1) → p5) → p2) ∨ p2) → p2) ∧ p5) → ((p2 → p2) ∨ p2)) ∧ p3) → p2) ∧ ((p3 ∧ p1) → (True → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807392764506845733675716776281 : (((p4 → (((((p1 ∨ p3) ∨ (False → (p3 ∧ False))) ∧ p4) ∧ True) → (((p1 ∧ ((p3 → p5) ∨ p3)) ∧ True) ∧ (p3 ∧ (p4 ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149551441497489062311020971692 : ((p2 ∧ (((p5 → p1) ∧ ((True ∧ ((p4 → (p1 ∨ p3)) → p3)) ∨ p4)) ∧ (((p1 → p1) ∨ p2) ∧ True))) ∨ (p3 → ((p5 ∧ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117416095850002688064285157317 : ((p1 ∧ (((((((p4 → p3) → p3) ∨ (p5 → (p4 → p3))) ∨ p3) → (p5 → (p1 ∨ (False ∨ p1)))) ∨ p3) ∨ (p3 → p1))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48435351272005406377611488910 : (((p4 → (((p3 ∨ ((((p1 → p5) ∨ True) ∧ (False ∨ p3)) ∧ (p1 ∧ True))) → (False ∨ True)) → (p5 → (False ∧ p5)))) → (False ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805060714310633032889974867999 : (((p3 → (True ∧ ((p1 → (True → p4)) ∨ ((True → p1) ∧ (True → ((False ∧ p4) ∧ (((p5 ∨ (p5 ∨ True)) ∧ True) ∨ (p2 ∧ p2)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179251454146522825768488768574 : ((p5 ∧ ((p3 ∨ p2) ∧ (p1 ∧ (((p1 → p4) ∨ (p4 → True)) → p5)))) ∨ (True ∨ ((p5 ∨ p5) ∨ (True ∧ (((False ∨ p3) ∧ p2) ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259091680751731926044811675479 : ((True → p5) → (((((True ∧ True) ∧ False) → False) → ((p5 → p1) ∧ p4)) → (((((p5 → p3) → p1) ∧ True) ∧ ((p4 ∨ p5) → True)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((True ∧ True) ∧ False) → False) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h4
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h12 : p5 := by
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h14 := h1 h13
    -- One of the premise coincides with the conclusion.
    exact h14
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h15 := h11 h12
  -- One of the premise coincides with the conclusion.
  exact h15
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200592486493384211861437839669 : ((True ∧ ((p1 ∨ True) → (p2 ∧ (p2 ∧ False)))) → (((p4 → ((p5 ∧ p1) ∨ (True ∧ (p4 → (p5 ∧ True))))) ∧ False) ∨ ((False ∨ p2) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p1 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111929835291456228944596086461 : (((((p4 ∧ p4) ∧ (p2 → (p3 ∨ ((p1 → p1) ∨ p1)))) ∧ (p3 ∨ (p1 ∧ (((p5 → (p5 ∧ p3)) ∨ p3) → False)))) ∨ p4) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_31578864917568936429852609856 : ((False ∨ (((((False ∨ (p3 ∧ p2)) ∨ p5) → ((p2 ∨ True) → p3)) → (((p2 ∨ p5) → True) → (p5 → (p4 ∨ (p3 ∨ False))))) ∨ True)) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683790577296887334856451799888 : (((((((((True ∧ True) ∧ (p1 ∧ p5)) ∨ p3) ∧ ((True ∨ p1) → True)) ∨ (p2 → p3)) ∨ p1) ∨ (p4 → ((p2 ∨ (True ∨ False)) ∨ p2))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_504508221991349051496802604781 : ((((False ∨ (p5 → p3)) → ((((((p5 ∧ (p1 ∨ p4)) ∧ (p3 ∧ p1)) ∧ ((p1 ∨ p3) ∨ (p3 ∧ True))) ∧ False) ∨ (p1 → p1)) ∨ p4)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158601235369262056733039477669 : ((False ∧ ((True ∨ ((p2 ∧ (((((p1 ∨ False) ∨ False) ∧ False) ∨ (p5 ∧ True)) → p5)) ∧ p2)) → p5)) ∨ ((((p1 ∧ p5) → p5) ∧ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191481466313760642322974254545 : ((True ∧ (((p2 → p5) → False) ∧ (p3 ∧ (p2 → p3)))) ∨ (((p1 → ((p2 → p1) ∨ (True → (p3 ∨ True)))) ∨ (p5 → True)) → (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171514008026482974577775064039 : ((((((p5 ∨ False) ∨ False) ∨ (p4 ∧ (((True ∧ False) → p5) ∧ p4))) ∧ p2) ∨ p4) ∨ ((p1 → True) → (((p4 ∨ p5) ∧ p3) → (p1 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686257831011188446319785726208 : (((((p2 → ((p1 ∨ False) ∨ (p1 ∨ (p4 ∧ p1)))) ∧ ((p2 ∨ p5) ∧ (p1 → (p1 → p5)))) → ((p2 → (p5 ∧ p1)) → (p4 → p5))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65711115784162919789779256122 : ((p4 ∨ ((((p2 ∨ True) → (((((p3 ∨ p5) → p2) ∧ ((p2 ∨ p1) → p2)) ∧ p1) → ((p2 ∨ p3) ∨ p5))) ∧ p1) ∨ (p1 → p1))) ∨ p2) := by
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
theorem thm_5_vars_196749795937999806532349805651 : ((((p2 → (p3 ∨ False)) ∧ (p3 → False)) ∧ p2) ∨ (p4 ∨ ((False ∨ (((p3 ∨ (False → (False → p4))) ∧ False) → p2)) ∨ ((True ∧ p3) ∧ p3)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_463180380100848351237877632625 : ((((((p3 ∧ False) ∨ p3) ∧ ((p1 → (p4 ∧ ((p5 ∨ p4) → (p2 ∨ False)))) ∧ False)) ∨ ((True ∨ p4) ∨ (((p4 ∨ p4) → True) ∧ False))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52243193469992797097878863643 : (((p5 ∧ ((p4 ∨ (((p4 ∨ p1) → False) ∧ p5)) → (p4 ∨ ((p3 ∨ p4) ∨ p1)))) → (p2 → (((p5 ∨ p4) ∧ p3) → (False ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757892508547434223330913437941 : (((p1 ∧ (p3 ∨ (p5 ∨ ((p1 ∧ ((p5 ∧ False) ∧ False)) ∧ (True ∧ ((p2 ∨ ((((p3 → True) → p5) ∨ p2) → True)) ∧ (False ∧ False))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44796592571806680709235292092 : (((((True → p2) ∨ False) ∧ ((p5 ∨ ((((p2 → p1) → True) ∨ p2) ∨ (p4 → p3))) ∧ ((p2 ∨ (p1 ∨ (p1 → p1))) ∧ True))) → p2) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h13 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h14 := h4 h13
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h16 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h17 := h4 h16
          -- One of the premise coincides with the conclusion.
          exact h17
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h6.left
          let h22 := h6.right
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h23 =>
            -- One of the premise coincides with the conclusion.
            exact h23
          case inr h24 =>
            -- Disjunctions on the left can always be decomposed.
            cases h24
            case inl h25 =>
              -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
              have h26 : True := by
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h4, we can now drive its conclusion.
              let h27 := h4 h26
              -- One of the premise coincides with the conclusion.
              exact h27
            case inr h28 =>
              -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
              have h29 : True := by
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h4, we can now drive its conclusion.
              let h30 := h4 h29
              -- One of the premise coincides with the conclusion.
              exact h30
        case inr h31 =>
          -- Conjunctions on the left can always be decomposed.
          let h32 := h6.left
          let h33 := h6.right
          -- Disjunctions on the left can always be decomposed.
          cases h32
          case inl h34 =>
            -- One of the premise coincides with the conclusion.
            exact h34
          case inr h35 =>
            -- Disjunctions on the left can always be decomposed.
            cases h35
            case inl h36 =>
              -- One of the premise coincides with the conclusion.
              exact h31
            case inr h37 =>
              -- One of the premise coincides with the conclusion.
              exact h31
      case inr h38 =>
        -- Conjunctions on the left can always be decomposed.
        let h39 := h6.left
        let h40 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h39
        case inl h41 =>
          -- One of the premise coincides with the conclusion.
          exact h41
        case inr h42 =>
          -- Disjunctions on the left can always be decomposed.
          cases h42
          case inl h43 =>
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h44 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h45 := h4 h44
            -- One of the premise coincides with the conclusion.
            exact h45
          case inr h46 =>
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h47 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h48 := h4 h47
            -- One of the premise coincides with the conclusion.
            exact h48
  case inr h49 =>
    -- False on the left can always be used.
    apply False.elim h49



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68646417541359286591724212395 : ((p4 → (((p5 ∨ ((True ∧ p2) ∧ (((p2 ∧ (((p1 → (False ∨ p5)) → p5) ∧ ((p3 ∨ p2) → True))) ∧ p4) ∨ p5))) → p5) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41482704614478207619641552975 : ((((p1 ∧ (((((p2 → (p3 → True)) → p2) ∨ p1) ∧ p5) ∧ False)) ∨ (((p1 ∨ ((p3 → (p3 ∧ p3)) → p4)) → p1) → True)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803165582788064757967408084473 : (((p3 → (((((p3 ∧ (True → (p4 ∨ (((p4 ∧ p5) ∧ (p1 ∨ (p1 ∧ (p4 → False)))) ∨ (False → True))))) → p1) ∨ p2) ∧ False) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111388271317250897110308647921 : (((False ∨ (False ∨ ((True ∧ ((((p5 ∧ (p3 ∧ (p4 ∨ p3))) ∨ ((p4 → p5) ∧ (p3 → p1))) ∨ p4) ∧ p4)) ∧ p2))) ∧ True) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_92723433492919025292816416037 : (((p3 → True) → ((((p1 ∨ ((p3 ∧ ((False ∨ (p4 → p4)) ∨ p5)) ∧ ((p2 → False) → False))) ∧ p1) ∨ ((p2 ∧ p4) → p3)) ∧ False)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56101215004220000699219804287 : ((((p4 ∨ p2) ∧ (p2 ∨ p4)) ∨ ((p5 ∧ ((p5 ∧ ((p2 ∨ p3) ∧ (True → p4))) ∧ ((p2 ∧ p4) ∧ False))) ∨ (p3 → (p3 → True)))) ∨ p2) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59338375016298216177702258212 : (((p4 ∨ p5) ∨ (p4 → ((p4 ∧ (p5 ∧ (p5 ∨ (p1 → (p2 ∧ (False ∧ (p2 ∧ (False ∧ (True ∧ p5))))))))) ∨ (True ∨ (p5 ∨ p3))))) ∨ p1) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122025426898380441636350699920 : (((p5 ∨ (p3 → (p3 ∧ (((p3 ∧ True) → p4) → (p1 ∧ (((p3 ∧ (p5 → ((p2 ∧ p4) ∧ p2))) ∧ p5) ∧ p2)))))) → p5) → (p4 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251707047807853682450674396786 : ((p3 → p2) ∨ (True → (p4 ∨ ((p4 ∨ (p3 ∧ (p4 ∨ (((p2 ∧ (p2 ∧ ((True → p3) ∧ (p1 ∧ p3)))) ∧ False) ∨ p1)))) ∨ (True ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127227273398207605511549139670 : ((p1 ∨ (p4 ∧ ((True → p1) ∧ (True → ((False → (p4 → p5)) ∧ ((p1 ∧ ((p2 → False) → p1)) → (p4 ∨ (p4 → p3)))))))) → (p4 → p1)) := by
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
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56718765841698496148463871174 : ((((False ∨ False) ∨ p1) ∧ (((p1 ∧ p1) → (p5 → True)) → ((p2 ∧ (p5 ∨ p1)) ∨ ((p5 ∨ p1) ∧ ((p3 ∧ p4) → (p2 ∧ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198247574473551626058920348927 : ((True ∧ (p5 ∨ (p5 ∨ ((p2 ∨ p5) ∨ p1)))) ∨ (((p3 ∨ (p5 ∨ p3)) ∨ ((p1 ∨ (False → p2)) ∨ (p2 ∨ (p2 → (True ∧ True))))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_775147163876579716394786917898 : (((False ∨ ((p5 ∧ False) ∨ ((((True → True) ∨ p5) ∧ p2) ∨ (((p3 → ((False ∨ (p1 → p3)) → p1)) ∨ (p4 → False)) ∨ (p2 ∨ True))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133642165620379548087422716095 : (((((((p5 ∨ (p4 ∨ (p5 → p4))) ∨ (((p2 ∧ (p2 ∧ p2)) ∧ p4) → False)) ∨ p3) ∨ p4) ∧ (False ∨ p3)) ∧ p2) ∨ (p3 ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759797392760727337059804959177 : (((p2 ∧ ((True ∨ (p1 → (((p2 ∨ (p1 → p1)) → p3) → p3))) → ((((p1 ∨ (p1 ∧ (p3 ∨ p4))) ∧ (p4 → p2)) ∨ p5) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724521219607398533382147470238 : ((((False ∨ (p2 ∨ p4)) ∧ (p1 → (((((p5 → p3) → (p2 ∧ p3)) ∧ True) → p4) ∧ ((p5 ∧ p2) ∧ (p5 ∨ (p3 → (False ∨ True))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337345358232945048694400999824 : (p1 → ((((((p5 ∧ ((p3 ∨ p5) → p5)) ∨ p4) → p4) ∧ (((p1 ∨ p1) → p2) → ((p3 → p5) ∨ p2))) ∨ p3) ∨ ((p2 ∨ p1) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43857377941341115755784334189 : (((((p1 → (((False ∧ ((p4 ∨ p3) ∧ p2)) ∨ (p4 → p4)) → (p3 ∨ p2))) ∨ (False → ((p5 → p5) ∧ p3))) ∧ (p1 → p3)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



