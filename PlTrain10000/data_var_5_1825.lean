variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185263679517819905618229754917 : ((p1 ∧ ((p1 → p5) ∧ ((p2 ∧ (p5 ∧ (p4 ∨ True))) ∨ p1))) ∨ ((p1 ∨ True) ∨ ((((((p4 → True) ∨ p5) ∧ False) ∧ p3) → p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42119726875604297343137068117 : ((((True ∨ True) → (((True ∧ True) ∨ p4) → (((p3 ∨ p1) ∨ (False → (((p4 ∨ (p4 → p1)) ∨ p5) ∨ (p1 ∨ p4)))) → False))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136314450644160429427865505628 : ((((p2 ∨ (p5 ∧ False)) ∨ p3) ∧ ((((p4 → p3) ∨ ((p3 → p1) → True)) ∨ (p5 ∧ p1)) ∧ ((p3 → p4) ∨ p3))) ∨ (p1 ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588062065559254349916626639873 : (((((((((p1 ∧ (p2 ∨ (p2 ∨ True))) ∨ p2) → (p1 ∧ True)) ∧ (p3 ∧ p5)) ∧ (p4 → (((p5 ∧ p1) ∧ False) ∧ p3))) ∨ False) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_237885589622699058505992889588 : ((True ∨ True) ∧ ((p5 → (((False ∧ ((((p1 ∧ (p2 → p2)) ∧ (p1 ∧ (p4 ∨ p3))) ∧ (p5 → False)) ∧ p2)) ∧ p5) ∧ True)) ∨ (p1 → p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310384195029722771997126581795 : (p2 ∨ (((((False ∨ p5) ∧ (p5 ∧ True)) ∨ p5) ∨ True) ∨ (((p5 ∧ (True → (p3 ∨ (((p3 → p3) ∧ (p4 → False)) ∨ p1)))) ∨ p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116041423059374330193531171835 : (((p4 ∨ (True ∧ (p1 → p5))) → ((((p1 ∨ (((p1 ∨ True) ∨ p2) ∨ True)) → ((p2 ∧ True) ∧ p2)) ∧ p5) → (p5 → p2))) ∨ (p3 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h1
  case inl h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : (p1 ∨ (((p1 ∨ True) ∨ p2) ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h13 : (p1 ∨ (((p1 ∨ True) ∨ p2) ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h14 := h4 h13
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55657419422248544337011983646 : ((((p4 ∧ (False ∧ True)) ∧ p3) ∧ ((((p5 ∧ p3) ∧ (p3 → p2)) → (p3 ∧ ((((p2 ∧ p3) ∨ True) → True) ∧ p4))) ∧ (p4 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60473760934849946755806586173 : (((p5 → p4) → (p4 ∨ (p1 → (((((True → p2) ∧ ((p4 → p4) ∧ (p4 ∨ (((p3 ∨ p4) → True) ∧ True)))) → True) → p3) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19476287593286114665993300634 : (((((((((p5 ∨ p5) → False) ∧ (False → (p4 ∧ True))) ∧ p3) → False) ∨ p2) ∧ p3) ∨ ((False → p3) ∨ ((p5 ∨ (p5 ∧ p4)) → p4))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47316072453628779531714112659 : ((((p2 → (p5 ∨ p3)) ∨ ((((p2 → p3) → False) → (p2 → (p3 ∨ (((False ∧ False) → p5) → (p4 → p2))))) → p5)) ∨ (True ∧ True)) ∨ p4) := by
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
theorem thm_5_vars_512581262490591008121074367 : ((((True → False) ∧ ((False → p1) ∧ (((p1 → p5) ∨ p2) ∧ (False ∧ (True → (p5 → ((p1 ∧ p1) ∨ (True → p4)))))))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259143944415509028531032024883 : ((False → True) → (((((True → p2) ∨ (p5 → p4)) → False) → (False ∨ (p5 ∨ (p2 ∧ ((p3 → (False ∧ p2)) ∧ p4))))) ∨ ((False ∧ True) → p3))) := by
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
theorem thm_5_vars_697656736220760162479415601742 : ((((p4 ∨ ((False ∧ p1) ∨ ((p1 ∨ p1) ∧ (p3 ∨ (p4 ∧ p2))))) ∧ (False ∨ ((p3 ∧ p2) → ((p1 ∨ ((p4 ∨ p4) → p4)) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157501250124570493210465850633 : ((((False ∧ False) ∨ (((p4 ∧ p3) ∨ ((True ∧ p2) ∧ p5)) → (p3 → (False ∧ p5)))) ∨ (p1 → p1)) ∨ (((p1 ∨ p5) ∨ (False → p2)) ∨ p3)) := by
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
theorem thm_5_vars_137539622544837989831247515011 : ((p5 ∧ (p1 → ((((p1 ∧ ((((p4 ∧ p2) ∧ (True → p2)) → p2) → False)) → (p4 ∨ p2)) ∨ False) → (p4 → p3)))) ∨ (False → (p2 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198954954993397761764741429615 : ((p4 → (p1 ∨ ((p5 ∧ False) ∨ (p3 ∧ True)))) ∨ (True → ((p1 ∨ (((True → p3) → ((p2 ∧ (p3 ∨ p1)) ∨ p3)) ∨ False)) ∨ (p1 → p5)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41482917271406127450901955041 : ((((p1 ∧ (True ∧ (p3 ∧ ((True ∨ (True ∨ p3)) → (False ∧ p5))))) ∨ (p4 ∧ ((((p4 → p4) ∨ True) ∧ (p1 → True)) ∧ True))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217040268299739420564608690427 : ((((p2 ∨ p1) ∧ p2) ∨ True) → (p3 ∨ (p3 ∨ ((p2 ∧ p2) ∨ (p1 → ((p3 ∨ p2) ∨ ((((True ∧ p5) → (p4 → False)) → False) → p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h4
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h4
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136743399862594272434269635388 : (((False ∨ p4) ∧ (p4 ∧ ((((p4 → p4) ∧ ((p2 ∨ ((p4 ∨ p3) → p4)) ∧ False)) ∨ (p4 ∨ (p1 ∨ p5))) → p1))) ∨ ((p3 → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165210983683754451339365324899 : ((((p1 → ((True ∧ (p2 → p5)) ∨ ((p5 ∨ p3) ∧ False))) ∧ (p1 ∧ p1)) ∨ (p1 ∨ True)) ∨ (False ∧ ((False ∧ (p3 → (p3 → p1))) ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791321463598605732498347949615 : (((True → ((((p3 → (((p1 ∧ (p3 ∧ ((p4 → p5) ∨ p1))) → (True → (False ∧ p2))) ∧ p5)) → (p3 ∨ (p4 ∨ True))) → p3) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_262226378855510019712276893749 : (True ∧ ((((((p1 ∧ ((False ∨ p3) → p2)) ∧ False) ∧ ((((True ∨ p2) ∧ True) ∧ p4) ∨ ((p2 ∨ p2) ∧ p3))) ∧ p1) ∨ (p5 ∨ True)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201775474886866425891180812017 : (((((p4 → p4) ∧ p1) → p1) ∨ p2) ∧ ((((p5 → p5) ∧ ((p5 → ((p3 ∧ p5) ∨ p3)) ∨ p1)) ∧ (p3 ∨ p2)) ∨ ((False ∧ p2) → p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56468504384708928994789651944 : ((((p1 ∨ False) → (p2 → p4)) → ((((p4 → False) ∧ (False ∧ p1)) ∧ (((True ∧ False) ∧ (p5 ∨ (False ∨ (p2 → p4)))) ∨ p1)) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588893102632778672566103377055 : (((((p3 ∨ ((p3 ∨ (p2 ∧ ((p5 → (p1 ∧ p4)) ∧ (((p4 ∨ (p1 → p3)) ∨ p1) → (p1 ∨ p1))))) ∧ (p1 → p5))) ∨ p4) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_36023447537701701583147335533 : ((p3 → (((p2 → p3) ∧ (True ∨ True)) → ((p4 ∨ ((p3 → p2) → (True ∧ (p2 ∨ ((p4 ∧ ((p4 ∨ p3) → True)) ∧ False))))) ∨ p1))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55586887793897136728960107136 : (((p3 ∨ ((False ∨ (True → True)) ∨ False)) → (p2 ∧ (((p2 ∧ p4) ∧ (((True → p5) ∨ (True → p4)) ∨ p3)) ∨ (p5 ∧ (p3 ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346370209971350405082640344506 : (p3 → ((p2 ∧ ((((p5 ∨ (p5 → (((p5 → p4) ∧ (p2 → (p2 ∨ p3))) ∧ False))) ∧ p4) → p2) ∧ ((p5 ∧ True) ∨ p5))) ∨ (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94418465950761439693339733591 : ((p2 ∧ ((p3 ∨ True) → ((True → True) ∧ ((((p3 ∧ True) → (False → p3)) ∧ (((((p3 → True) ∨ p4) → p2) → p4) ∨ False)) ∧ p5)))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : (((p3 → True) ∨ p4) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h2
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h14 := h9 h10
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185088770360101399184697454591 : (((p3 ∨ p3) ∨ (((((p2 ∧ p2) ∨ p4) ∧ p2) ∨ p2) ∨ False)) ∨ ((p1 → True) ∨ (True ∨ (((False → (p4 ∧ p5)) ∧ True) ∧ (False → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177923086599557907818823709818 : (((((p3 ∨ (False → p3)) ∧ (p4 ∨ p2)) → ((p4 → p1) → p4)) ∨ p3) ∨ ((p1 → (True ∧ p4)) → ((True ∧ (p4 → p4)) ∨ (p4 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603556206113753309273028738342 : ((((p3 ∨ ((False → True) → (((((p1 → ((False → p4) ∧ p4)) ∨ ((p5 → p4) ∨ p2)) ∨ (True ∧ (True → p2))) ∨ p3) → p4))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727603265809953253689269168133 : ((((p5 ∧ (p1 ∨ p4)) ∨ (((p3 → (((p4 → p5) ∧ p5) ∧ (p3 ∨ p4))) ∨ (p3 → p2)) → (p3 ∨ (p2 ∧ (p2 → (p5 ∨ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54159660013908153270799965305 : (((p4 → (False ∧ ((p2 ∧ (p2 → p4)) ∨ (p5 ∨ False)))) → ((p5 → p2) → (((p2 ∨ True) ∨ True) → ((True ∧ True) ∧ (p4 ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775847240450033411340151312380 : (((False ∨ (True → (((((p4 ∧ p2) ∧ p1) → ((p5 ∨ ((p5 ∧ p4) ∧ p5)) → False)) ∧ p2) ∨ (p4 ∨ ((p2 → p2) ∨ (p4 → p5)))))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318871550487593421894613975805 : (p4 ∨ ((((p3 → p5) → ((((True → p5) ∨ p3) → ((p4 ∧ p2) ∨ p2)) → p1)) ∧ (p4 → ((True → p1) ∨ p3))) ∨ ((False ∧ True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54667589537502971496350804592 : ((((p3 → (((p1 ∧ p1) → p3) → False)) ∨ p5) → ((((p4 ∨ p3) → False) ∨ (p3 ∧ ((((p3 → p4) → p4) ∧ p4) → False))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712430203016645928206531235908 : (((((p1 ∨ (p5 ∧ p2)) ∧ (p4 ∨ p2)) ∨ (False ∨ ((p3 ∨ (False → True)) ∨ ((True ∧ (True ∧ (p4 ∨ p4))) ∧ ((p2 → False) → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124112193118919684889099703287 : ((((((p4 ∨ p5) → p2) ∨ (True ∧ True)) → (p5 ∧ False)) ∧ ((p4 → ((True → (p4 ∧ p1)) ∨ (p5 ∨ False))) ∧ (p3 → True))) → (p3 → p4)) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : (((p4 ∨ p5) → p2) ∨ (True ∧ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135761261456018328682656301722 : (((p4 ∨ (((p5 ∨ p5) ∨ (p2 → ((False → p5) → p1))) ∨ (p5 ∨ False))) ∨ (((p2 ∨ False) ∨ False) ∨ (p2 ∧ p5))) ∨ ((p3 ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712238436823765920652671324384 : ((((((p1 ∧ p5) ∧ (p1 ∧ p4)) → False) ∨ ((((p4 ∧ True) ∧ ((p4 ∧ (((False ∨ False) → p5) ∨ (False ∧ p2))) ∨ p3)) ∨ True) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251376516256021420921342946967 : ((p2 → p4) ∨ (((True ∨ p5) → (p4 ∨ (p4 → (((p4 ∨ False) → (p5 ∨ p1)) ∨ False)))) → ((True ∨ p5) → ((p2 ∧ (p4 ∧ True)) ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609664426368110651406405463465 : (((((p1 ∨ (((((True → (True ∧ (True ∧ p1))) ∧ False) ∧ (True → (((p5 → p1) ∨ (p5 ∨ p2)) ∧ p3))) ∨ p3) ∧ p3)) ∨ p5) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55965070846086765505055352747 : (((((False ∧ True) ∨ p4) ∧ p3) ∨ (False ∨ ((False ∨ p5) ∧ ((p4 ∧ (p3 ∧ (((p4 ∧ p5) ∧ p5) → True))) ∧ (p3 → (p1 ∧ True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147635837286744449932334901432 : ((((((p5 → False) ∨ False) ∨ ((((p4 ∨ p1) ∧ p4) ∧ ((p4 ∨ True) ∧ p5)) ∨ (False ∧ p1))) → p4) → p1) ∨ (False ∨ (False → (p5 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187534391436478719992468090086 : ((p2 ∨ (((p4 → (((True ∧ True) ∨ True) → p4)) → True) ∧ p5)) → ((((((True ∧ (p1 ∨ True)) → (p4 ∧ p2)) ∧ False) ∧ p2) ∧ p5) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49024087824708252785481120329 : ((((((p1 → False) → ((p5 → (p2 → p1)) ∨ (p3 → True))) → ((True ∨ p2) ∧ ((p4 → p5) ∨ p5))) → p5) ∨ ((p4 ∨ p2) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41766784582236454166953281588 : ((((p2 ∧ ((p1 ∨ p1) ∧ p4)) ∨ (((p2 ∧ p3) ∨ ((p4 ∧ p5) ∧ (False → ((p3 → p2) ∨ ((p2 ∧ p1) ∧ False))))) → p3)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629948470606059259589874770467 : (((((((p3 ∨ (False → (p1 → p1))) → p3) → (p3 → ((p5 → p4) ∧ (((p4 ∨ p4) ∨ (p1 → True)) → (True → p5))))) ∨ p3) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147614535829720952093741129423 : ((((True → ((False ∨ p2) → (False ∨ (((p1 ∨ True) ∧ ((p4 ∨ False) ∨ (p4 → p3))) → False)))) ∨ p2) → p5) ∨ ((True → p3) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64949808566329602351918015982 : ((p2 ∨ ((((True ∧ p2) ∨ (p4 ∧ (True ∧ (p5 ∨ True)))) ∧ True) → ((((p4 ∧ ((True → p3) ∨ (False → True))) ∧ False) ∧ p4) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232700385425901975805256053482 : ((p1 ∧ (p1 ∨ p3)) → ((p3 → (((p2 ∨ p2) ∧ ((p2 → (p2 ∧ (p2 → p4))) → p4)) → (False ∧ True))) → (p2 ∨ ((True → p5) ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646086382433551391011629278238 : ((((True → (p3 ∨ (((((True ∧ p3) ∧ True) → True) ∧ (p4 → (p3 ∧ ((p1 ∧ ((p2 ∨ p3) ∨ p3)) ∨ (p5 → p1))))) ∨ True))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230140834373734990367737406222 : (((p4 ∧ p1) ∧ p2) → (((True ∧ (p3 → p2)) → (((p1 ∨ p4) ∧ (p5 ∨ (p5 ∨ ((False ∧ p5) ∧ (p2 ∧ p1))))) ∨ (p3 ∧ p2))) ∨ p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60820606280627980257108535989 : ((True ∧ (p4 ∧ (p4 → ((True → ((p4 → ((p3 ∨ p4) → (p1 → False))) → ((((p3 ∨ p2) ∧ False) ∨ (False ∨ p5)) ∨ True))) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_485404017309619371651725547202 : (((((((p1 ∨ False) ∧ p2) ∧ p5) ∨ p3) ∨ (p1 → (p2 ∨ ((True ∧ ((p1 ∧ ((p2 ∧ (p3 ∧ False)) → p3)) ∧ (False ∨ False))) → p5)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699128704471976291004381200241 : ((((True → ((p3 → ((p5 ∨ p2) → p2)) ∧ (True → (p4 ∨ p3)))) ∨ ((((False → p5) ∧ p5) ∨ ((p3 → p5) → (p2 → p5))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226544678008441402064635674879 : (((p3 → p5) ∨ p5) ∨ (((((((p3 ∧ p1) ∨ p3) ∧ (p1 → p4)) ∨ (p2 ∧ p2)) → p2) ∨ True) ∧ ((p1 ∨ ((True → True) → p2)) ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193477231014532454631116751665 : (((p4 ∧ p3) ∨ ((p1 ∨ ((True ∧ p4) ∨ p1)) ∧ p3)) → (((((p3 ∧ (((True ∧ p4) ∨ p4) → p5)) → p5) ∧ True) ∧ (p5 ∨ p4)) ∨ p3)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144062461525904166945509951200 : (((p1 → ((((((p4 → p3) → p2) → p3) → False) ∧ ((p4 → p1) ∧ (p4 ∨ p1))) ∨ (True ∨ p4))) ∨ False) ∧ ((False ∧ (p2 ∧ p5)) → p2)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680797404303515286998378307055 : (((((p3 ∨ (p4 → p3)) ∧ (((False → ((p1 ∧ False) ∧ p3)) ∧ (True → p4)) ∨ (p4 ∨ (p3 ∧ False)))) → (p4 ∨ ((p2 ∨ p1) ∨ p5))) ∨ p5) ∧ True) := by
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
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h9 := h7 h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- False on the left can always be used.
        apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h19 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h20 := h18 h19
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h22
      case inr h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- False on the left can always be used.
        apply False.elim h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148165613943648522162988966997 : (((((False ∨ p5) ∧ ((False ∨ (p5 → p3)) ∨ (((p3 ∧ p5) → p4) ∧ p2))) ∧ True) ∧ ((False ∧ False) ∧ True)) ∨ ((True → (True → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38471054160019497649148434660 : (((((((((p4 → p4) ∧ False) ∧ (p2 → False)) ∨ p5) ∨ p3) ∧ p2) ∧ ((p5 → (p5 ∨ ((p5 → p4) ∨ (True → False)))) ∨ p4)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_959616383047262845247029650264 : ((((p3 ∧ True) ∧ ((p4 ∨ ((((p5 ∧ p1) ∨ (p5 → p4)) ∨ True) ∧ p3)) → ((p2 ∧ False) ∧ (p5 ∧ (((p3 ∧ True) → p3) ∧ p2))))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : (p4 ∨ ((((p5 ∧ p1) ∨ (p5 → p4)) ∨ True) ∧ p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322205326222122544054123540354 : (p5 ∨ (((((p4 ∨ (p4 → (False ∨ (p5 → (((True ∧ p2) → (True → p4)) ∨ p5))))) → ((p3 ∧ (p3 → p4)) ∧ True)) → p2) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616283425416808752250832359770 : ((((((((p2 ∧ p3) ∧ (p4 ∨ False)) ∨ (p3 → p1)) ∧ (p1 ∨ p4)) ∨ (((False ∧ True) ∧ (p2 ∨ (p4 ∨ (True ∨ False)))) → False)) ∨ p1) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781070141362212877514082487814 : (((p2 ∨ ((p4 → p2) ∧ ((((p5 ∧ p1) ∨ ((False ∨ p2) → (p1 ∨ ((p3 ∨ (p5 ∧ (True → p1))) ∧ (p2 ∧ False))))) ∨ True) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136945555142350628870791693147 : (((p5 → False) ∨ (p2 → ((p4 ∨ (p4 ∧ (((((p5 ∨ False) → ((p3 ∨ p4) ∧ p5)) ∧ p4) ∨ p3) ∧ True))) ∧ p4))) ∨ (False → (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193455743498462718555398861973 : (((p5 → p3) ∧ ((p3 ∧ (p2 → p3)) ∧ (p1 → p2))) → ((p4 ∨ (False ∨ (p5 ∨ ((False ∨ ((p1 ∨ p5) → p2)) ∧ (p2 ∨ p5))))) ∨ p3)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52662239305544937226176902709 : (((p4 ∧ ((p4 ∧ (((p2 ∧ ((p5 ∧ p4) → p2)) ∨ p3) ∧ False)) → p4)) ∨ (p4 ∧ (((True → (p1 → p1)) → (True → p2)) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197767391198604500292893138244 : (((p3 ∨ (p2 ∧ p1)) ∧ ((p3 ∨ p1) ∧ True)) ∨ (((((p5 ∨ True) ∨ True) ∨ ((((False → p2) ∨ (p1 ∨ True)) ∧ False) ∨ p2)) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624499230982888527591284239721 : ((((p4 ∨ (((p4 ∧ (((False ∧ (((False ∨ p1) ∨ (p5 ∨ p5)) ∧ p3)) → True) ∨ (p4 ∧ (p5 ∨ False)))) ∧ (p2 ∧ p1)) ∨ p5)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50762485301133642756512070325 : (((True ∨ (((p5 ∨ (p4 ∧ ((p4 ∨ p1) ∧ p4))) → (True → True)) ∨ ((True ∨ p2) ∨ (p3 ∧ False)))) → (((p1 → p2) → p2) ∨ True)) ∨ p4) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- False on the left can always be used.
        apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136405985963138050778326078763 : (((p2 → ((p5 ∧ True) ∧ p1)) ∨ ((p1 → (False ∨ ((((p3 → p5) ∨ (False ∨ p1)) → p4) ∨ p1))) ∨ (p2 ∧ p3))) ∨ (p4 → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142482196781477893635772159913 : ((p5 ∧ ((p4 ∨ p4) ∨ (p5 ∨ ((((p2 → ((p4 ∧ p3) ∨ True)) ∨ ((False ∨ (p4 ∧ p3)) → False)) → p5) ∨ p4)))) → ((p1 ∧ p1) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
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
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43434826669414196267526069074 : ((((((False → (p4 ∧ p2)) ∨ p3) → (((((p3 → (p4 → (True → p3))) ∧ p4) ∨ p1) ∧ (p2 → True)) ∨ (p3 → False))) ∨ False) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608635383800069216160235360240 : (((((((((((p1 ∧ ((p4 → (((False ∧ p1) ∨ p1) ∨ True)) → p4)) ∨ p5) ∨ True) ∨ p5) ∨ p3) ∧ p3) ∨ (p2 → p5)) ∨ p4) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339805645211101167894956968845 : (p1 → (p5 ∨ ((p1 ∧ (True ∧ ((False → False) ∨ ((((p2 ∨ False) ∧ p2) → p1) ∨ p1)))) ∧ (((((p3 → p5) ∨ p1) ∧ p2) → p3) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52246699759472479120908813750 : (((True ∨ ((p2 ∧ (p1 ∧ p2)) → ((((p5 ∨ p3) ∧ True) ∧ p5) ∨ (p2 ∨ p1)))) → (((((p2 ∧ False) → p5) ∨ True) → p3) ∨ True)) ∨ p5) := by
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
theorem thm_5_vars_149416072132753841188863610364 : ((True ∧ ((((p3 ∨ p1) ∧ (p3 ∧ p1)) ∨ p1) ∨ ((p2 ∧ (True → (True ∨ p2))) ∨ ((p4 ∨ p5) → p3)))) ∨ (p3 ∨ (p3 → (p1 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173854777796329182149724619845 : ((((((p2 ∧ (False → (False ∨ ((p3 ∧ p2) ∨ p4)))) ∧ p2) ∧ p1) ∧ p1) → p4) → ((p4 → (False ∧ False)) ∨ ((p1 ∧ (p2 ∨ False)) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54052439965714708190409368289 : ((((p2 ∨ ((p3 ∧ p5) → p1)) ∨ ((p5 ∧ p2) ∧ p5)) → (((p5 ∧ p2) ∧ (p2 → (p3 ∨ p5))) → (((p1 ∧ p1) ∧ p2) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262146735863529988956253919582 : (True ∧ ((((p5 ∨ ((((True ∧ ((True ∨ (p1 ∨ False)) → True)) ∨ p2) → ((p2 ∧ (p2 → (p2 → False))) → False)) → p5)) → False) ∨ True) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262434684182159334026833272306 : (True ∧ ((p4 ∧ ((((p5 → (True → False)) → p1) ∨ (p3 ∨ (True ∧ p2))) ∨ (p1 → (((False → True) → p5) ∨ (p3 ∧ (p2 ∨ p3)))))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152059274337619751520383979358 : (((((p4 ∨ (p3 → p1)) → (True ∧ p4)) → (p2 → p3)) ∨ (((True ∧ p1) → p4) ∧ ((p4 ∧ p5) ∨ p5))) → ((p1 ∧ p1) → (p4 → p1))) := by
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
  cases h1
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655107348884677211328775316732 : (((((p2 ∨ ((p5 → p5) → ((((((p1 ∨ (False ∨ False)) → (False ∧ p3)) → p5) ∨ (True ∨ p3)) ∨ False) → False))) → p4) ∨ (p4 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702944195889229955780951159293 : ((((((p5 ∧ p5) ∧ p4) ∨ (((p3 ∨ p4) ∨ p2) ∨ p2)) ∨ (False → ((p3 → False) → (((p3 ∧ False) ∨ ((p1 ∧ p2) → p2)) ∨ True)))) ∨ p3) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197991577529607515103254565658 : (((p4 ∨ p4) ∧ (p2 → ((p2 ∧ True) ∧ p4))) ∨ ((p4 ∨ p5) → (True → (p2 → ((p5 ∧ p5) ∨ ((p3 ∨ (p2 ∨ (False ∨ p4))) ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119569497449211890346895220314 : ((p5 → (((p3 → (False ∧ (False ∧ p3))) ∧ False) ∨ ((True ∨ (((((p2 ∨ p2) ∨ p1) ∨ p1) ∧ (p2 ∨ p5)) ∧ p1)) → p3))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66339225694920136643151299147 : ((p5 ∨ (p3 ∧ (((True ∧ False) → (False → p1)) → ((False ∨ (p2 ∨ ((p3 ∨ (p1 ∨ True)) ∨ p2))) ∧ (((p5 ∧ p4) ∧ p2) ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_35998653745520374446557991545 : ((p3 → ((((p1 ∧ (p5 → p5)) ∧ (p4 ∨ p2)) ∧ p1) → (((False → (p2 ∧ (p4 → (True → p3)))) → (p5 ∧ (True ∨ p5))) ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114531874750131819799897067311 : (((p4 ∨ ((p1 ∨ ((p4 → p2) ∨ p1)) ∨ ((p2 ∨ ((True ∧ p2) → p3)) ∨ (False ∨ p2)))) → (p2 ∨ ((p5 ∧ p2) ∧ p2))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98803320156501589822986856220 : ((True → (((p2 ∨ ((((p1 ∧ (p5 ∧ (((p4 ∨ (True ∧ False)) → p2) ∨ (True → p1)))) ∨ p3) ∧ p4) ∧ (p3 ∨ p5))) → p3) ∧ False)) → p2) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172182228113243035060393231812 : (((p1 ∨ ((False → p1) ∧ (p3 ∨ ((p1 ∨ p2) ∧ p2)))) ∨ ((True → p5) ∨ p1)) ∨ (((True ∧ (p2 ∧ (p5 → False))) → True) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319871665782995053957046963824 : (p4 ∨ (((True ∧ False) ∨ (p2 ∧ p4)) ∨ ((p1 → ((True ∧ p3) ∨ (p4 → p1))) ∧ (((((p3 ∧ p4) ∧ True) ∧ (p4 ∧ True)) → False) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243010623431403539596528141543 : ((p4 → True) ∧ ((p4 → p1) → ((((False ∨ (p5 → p5)) → p4) ∨ p3) ∨ ((p3 ∧ p4) → (((p1 → (p4 ∨ (False → p1))) → False) → p2))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h7 : (p1 → (p4 ∨ (False → p1))) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h7
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164670042773491829166816345794 : (((((((True ∨ ((False → False) ∧ (p1 ∨ (p1 ∨ False)))) ∨ p5) ∧ False) ∨ p3) ∧ False) ∨ p4) ∨ (((False ∧ False) ∨ ((True ∨ p5) ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_486763455493302799475202086254 : ((((p4 ∨ (p1 → ((p3 → p3) → p4))) ∨ (p3 ∨ ((p4 ∨ (((p1 → (p2 → (True → (p3 ∨ True)))) → p1) ∨ False)) ∨ (False → True)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46382678342350430981409725594 : ((((False → (((((p5 ∧ p5) ∨ p3) ∨ p3) ∨ p2) ∨ True)) ∧ (p1 ∨ (True → ((p5 → ((p2 ∧ p5) → p4)) → p1)))) ∧ (True → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



