variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135711968500384239217825552770 : (((p3 ∧ (True → (p2 ∨ ((True → p1) → (p5 → ((p5 → False) ∧ True)))))) ∧ (p5 ∧ ((False ∨ (p5 → p4)) ∧ p2))) ∨ ((True ∨ p4) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81992305025048478711351018315 : ((((True → ((p5 ∨ p1) ∨ (True → False))) ∨ (p2 ∨ ((p5 ∨ p2) ∨ (True ∨ ((p2 ∨ p1) → (False → p4)))))) → ((p3 → True) → p3)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True → ((p5 ∨ p1) ∨ (True → False))) ∨ (p2 ∨ ((p5 ∨ p2) ∨ (True ∨ ((p2 ∨ p1) → (False → p4)))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p3 → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264776713828956297546144498253 : (True ∧ ((p4 → p4) ∧ (p2 → (((p2 → (False ∧ (((False ∧ p3) ∧ p4) ∨ False))) ∧ ((p3 → p1) ∨ ((p1 ∧ True) ∧ (p2 ∧ True)))) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962815140912646727017438801388 : ((((False → p3) ∧ (p3 ∧ (((((((p3 → (p4 ∧ p5)) ∧ p1) → (p3 → p2)) ∨ (p1 → p1)) → ((p5 ∧ p1) ∧ True)) → p3) → p1))) → p1) ∧ True) := by
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
  have h6 : ((((((p3 → (p4 ∧ p5)) ∧ p1) → (p3 → p2)) ∨ (p1 → p1)) → ((p5 ∧ p1) ∧ True)) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790631073185164161038544863911 : (((p5 ∨ (p4 ∨ ((((False → (False ∧ (p1 ∨ (True ∧ (False ∨ p5))))) ∨ (((True ∧ p4) ∨ p3) ∧ p5)) ∧ ((p3 → False) → p5)) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40406408243952543195247371457 : (((((((p3 ∨ ((p3 ∧ p5) ∧ (p3 → p3))) ∨ p2) ∧ (p2 ∧ (True ∧ (p3 ∨ (p3 ∧ p1))))) → ((p2 → False) ∨ p3)) ∨ p1) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59400320553368291898700085689 : (((True → p2) ∨ (p5 → (((p5 → p1) ∧ True) ∨ ((p3 → (((p3 ∧ False) → (p5 ∧ True)) → p2)) → (p3 ∧ (p3 ∧ (False ∨ False))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179455021254981730404221377482 : ((p5 ∨ ((p2 → (p2 → False)) ∨ (((p5 ∧ (False → False)) ∨ p2) ∨ p2))) ∨ (False → (True → (p3 ∨ ((p4 → (True ∨ p2)) ∧ (True ∧ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41446924907660773715599545597 : (((((((p2 → p3) → ((p4 ∧ (p3 ∧ p1)) ∨ p2)) ∨ p5) ∧ True) ∧ (((p3 ∨ True) ∨ ((False ∧ True) ∨ (True ∧ False))) → p3)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47079960601044927597960071000 : (((((((p2 ∧ (p4 ∧ ((p1 ∨ False) ∨ p4))) ∨ p4) ∧ (True ∧ ((False ∧ (p3 → p4)) → True))) → p5) → (p5 → p5)) ∨ (p3 → p2)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147632524734827365860219320792 : ((((((p2 ∧ (False ∨ ((p5 → p1) ∨ p3))) ∨ p5) → (p2 ∧ ((p1 ∨ (p1 → False)) ∧ p3))) → p3) → p3) ∨ (((p1 ∧ False) ∧ p2) → False)) := by
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
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2075471838298914509492863195 : (((((((p1 ∧ (False ∧ p5)) ∨ p1) ∨ p4) ∨ (p5 → (p3 ∨ p1))) ∨ (True ∧ p5)) → p5) ∨ (((p5 ∨ p4) → (True ∧ p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669406382522226130157954316473 : (((((((p1 ∨ ((p4 → ((p3 → p2) ∨ p3)) ∨ True)) → ((p2 → p4) → p2)) ∨ (p3 ∨ p3)) ∨ (p1 → True)) ∨ ((p4 → p4) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62972993270966718106212647616 : ((p4 ∧ (p2 ∨ (p1 ∧ ((p5 ∨ (p4 → ((((((p5 → p5) ∨ p2) ∨ False) → ((p4 ∨ p3) ∧ p3)) ∨ p2) → (False ∧ p3)))) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65995875699449330101014134969 : ((p4 ∨ (p4 → (((p5 → (p2 ∨ (((p3 → p2) → (p2 ∧ p1)) ∨ ((p3 → p1) ∨ (False ∨ p3))))) ∨ (p4 ∨ (True → p2))) ∨ p3))) ∨ p3) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707933726743455257419087488229 : ((((p5 ∧ (p3 ∨ ((p1 ∨ p5) ∨ (p5 ∧ True)))) ∨ ((((p4 ∨ p4) → p1) → (False ∨ (False → (p3 ∨ ((p2 ∨ p4) → True))))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205069217474561841510778426268 : (((p3 → (True → (p1 ∧ p2))) → p5) ∨ ((p4 ∨ False) ∨ (True ∨ ((((p4 → p3) ∧ (False → False)) → (p2 → (p2 ∨ (p2 ∨ p2)))) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135422940013858089266541542129 : (((p2 ∧ (p2 ∨ ((p2 ∨ ((True ∨ (p2 → False)) → (p1 ∧ (p2 ∨ p1)))) ∧ (True ∧ True)))) ∨ ((True ∨ True) ∧ p5)) ∨ (True → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54201966504287734928637955099 : (((((p3 ∧ p3) ∧ (False ∨ (False → True))) ∨ p5) ∧ ((((p1 ∨ p1) ∧ (p1 → (p4 ∧ False))) → ((p1 ∨ (p1 ∨ p3)) ∧ p4)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1460036431075631642573331726 : ((((p2 ∧ ((True → (p5 ∨ p5)) ∨ (p2 → ((True → p5) ∨ p2)))) ∨ (False ∨ ((p3 ∧ True) ∨ (False ∧ False)))) ∧ p1) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102745453013581361691315024697 : ((((p2 → (((p1 ∨ (p2 → (((p1 → p2) ∨ (p3 ∨ (p3 ∨ ((True ∨ p4) → p2)))) ∧ p2))) → p4) ∨ p2)) ∨ True) ∨ p2) ∧ (False → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65233232955073402958192918492 : ((p3 ∨ ((p2 → (False ∨ ((((p3 → p3) → True) → (p3 ∧ (p5 ∨ (((False → (p5 ∨ p3)) ∨ (p5 ∧ p3)) ∧ p2)))) ∨ True))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307119273031981353404516381955 : (p1 ∨ (False ∨ (((p3 → (p4 ∨ (((True ∨ p3) → p2) ∧ (((((p1 ∧ False) ∧ p1) ∨ True) ∨ p1) ∨ (p1 → (p4 ∧ p2)))))) ∨ True) ∨ p5))) := by
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
theorem thm_5_vars_64141153184134040374121596660 : ((False ∨ ((p4 ∨ (p4 → p2)) ∧ ((((p3 ∨ (p1 ∨ p2)) ∨ p1) → (True ∧ ((((p2 ∨ False) ∧ True) → p2) ∧ (p5 ∧ p3)))) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300997753850483515628935874020 : (False ∨ ((((p1 ∧ False) ∨ p5) ∧ ((((p5 ∨ p1) → p5) ∧ p3) ∨ False)) → ((((True → False) ∨ (p2 → False)) ∧ p3) ∨ (p2 ∨ (p1 ∨ p5))))) := by
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
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206467675471477222591221341102 : ((p4 ∨ (p4 ∨ (p4 ∨ (p1 ∨ p3)))) ∨ ((((p5 → (p3 → ((p3 ∧ (False ∨ False)) ∨ p1))) ∨ p4) ∧ ((p2 ∧ p4) ∧ (True ∧ p4))) → p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h6.left
    let h10 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h13.left
    let h17 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623579768598112033936696529033 : ((((False ∨ (p3 ∧ (p1 ∨ (p1 ∧ (p1 ∧ (False ∨ (p1 → ((((p1 → False) → (p1 ∧ p2)) → p4) → (p4 → (p4 → False)))))))))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68168114325023768942072288634 : ((p3 → ((True → (p2 → ((p3 → (p1 → (p2 → ((True → (p5 ∨ (p4 ∧ ((True ∨ p3) → p3)))) ∧ (p4 ∨ p3))))) ∧ False))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52120932546118505369813331160 : (((((True ∧ p4) ∨ ((p3 ∧ p3) → (p3 ∧ ((p1 ∨ p3) ∧ (False → p2))))) → False) → (True ∧ ((p4 ∨ (p2 ∧ False)) ∧ (p1 ∨ p2)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∧ p4) ∨ ((p3 ∧ p3) → (p3 ∧ ((p1 ∨ p3) ∧ (False → p2))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- False on the left can always be used.
  apply False.elim h9
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : ((True ∧ p4) ∨ ((p3 ∧ p3) → (p3 ∧ ((p1 ∨ p3) ∧ (False → p2))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h13
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h14 := h11.left
    let h15 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h15
    -- Implications on the right can always be decomposed.
    intro h16
    -- False on the left can always be used.
    apply False.elim h16
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h17 := h1 h10
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111563314036011158549052685741 : ((((((p3 ∧ (False → (p4 → True))) → p2) ∧ (((((p3 ∨ p5) ∧ p4) ∧ (True → (True ∧ p3))) ∨ True) ∧ p4)) ∧ True) ∨ p3) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585753703569189503016720774982 : (((((((p2 → (p2 ∧ False)) ∧ ((True ∨ (p3 ∨ (p3 → p2))) ∧ ((((p4 ∨ p2) → p4) ∧ True) → (p3 → True)))) → p5) ∧ True) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779296664106397400589202740919 : (((p2 ∨ ((p3 ∧ ((p5 → p5) → (True ∧ (((p3 ∨ p5) ∨ ((p3 → (False ∨ p2)) ∨ ((True ∧ (True ∨ p5)) ∧ p2))) ∨ True)))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64710303732270231176256271495 : ((p1 ∨ (p2 → ((((p5 ∨ ((True ∨ p3) → ((True → p5) → p5))) ∧ (True ∧ ((False → (p5 → p4)) ∨ False))) ∧ p1) ∨ (True ∧ True)))) ∨ p2) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181676522581259899959891472996 : ((p4 → ((((True ∧ p4) ∨ p2) ∧ p4) → (p4 ∨ (p5 ∨ (True ∨ p2))))) → (p4 → ((((p1 → p1) ∧ p3) → (p2 → (True → p1))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68789720350576767464702108672 : ((p4 → (((False ∨ (p2 → p4)) ∨ (p2 ∨ p5)) ∧ (((((((False → True) ∨ p3) → (p1 → False)) ∨ p2) → (p3 ∧ True)) ∧ p5) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585367391890239692201437306057 : ((((((((((p1 ∧ (p5 ∨ True)) ∧ p1) → True) ∧ (p2 ∨ (p2 ∨ False))) ∨ ((p5 ∨ p3) → (False ∨ (p3 ∧ p1)))) ∧ p2) ∧ False) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308554746634959003819917347406 : (p2 ∨ (((p5 ∨ ((p4 ∨ (p1 ∨ p2)) ∨ (p5 ∧ p1))) ∨ (((False → (p1 ∧ p4)) ∨ p5) ∧ (((p5 ∧ True) ∨ p1) → (True ∧ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2637369227977619996174577130 : ((True → (((p3 ∨ p5) ∨ True) ∨ True)) ∧ ((((((p4 ∨ p4) ∧ (p1 ∨ p5)) ∧ ((p3 → False) ∧ p5)) ∨ (p1 → p4)) → p5) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40766553085026486992352585717 : (((((True ∨ p4) → ((False → ((p1 ∨ False) → (p5 → (p4 ∧ False)))) → ((((p1 ∧ p2) ∨ (p1 ∨ p1)) ∧ p4) ∨ p2))) → p2) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314423648581502799558941173681 : (p3 ∨ ((((False ∨ (False → True)) ∧ (p1 → (p2 → p5))) → (((p2 ∧ p5) ∧ (p4 ∨ (p4 → p2))) ∨ True)) ∨ (((p3 ∨ True) → p4) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178054155984030811539754648104 : ((((p2 → (True → (p2 ∧ ((p3 ∧ p2) ∨ (False → p4))))) ∧ p3) → False) ∨ (False → ((p4 → (True → (False ∧ (p2 ∧ (p5 ∧ True))))) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767768724080535655075953727708 : (((p5 ∧ ((((True → ((p4 ∨ (False ∨ p5)) ∨ p1)) ∨ (((((p3 ∧ (True → p3)) ∧ p5) → p3) → False) → (True → True))) ∨ p3) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2270359835817139909947725831 : (((((True ∧ p2) → (False ∧ (p1 ∨ (p3 ∧ p4)))) → (p5 ∨ p4)) ∧ p1) ∨ (p3 → (p2 ∨ (p5 ∨ (p5 → ((True ∧ False) ∨ True)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317711302223370011392399739342 : (p4 ∨ (((p5 ∧ ((p1 ∨ p2) ∧ (p2 ∧ (((((p5 → (p2 ∨ (p2 → (p1 ∨ p3)))) ∨ p3) → p5) ∧ p4) ∧ p2)))) ∨ (p3 ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153132101854193744145708176412 : ((p4 ∧ (p2 ∧ ((((False ∨ (((p5 → p3) ∧ True) ∨ (p5 ∧ ((p4 → p4) ∨ True)))) ∧ p4) ∨ p3) ∨ p5))) → (p3 → ((False ∨ True) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h23 := h1.left
  let h24 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h25 := h24.left
  let h26 := h24.right
  -- Disjunctions on the left can always be decomposed.
  cases h26
  case inl h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h31 =>
        -- False on the left can always be used.
        apply False.elim h31
      case inr h32 =>
        -- Disjunctions on the left can always be decomposed.
        cases h32
        case inl h33 =>
          -- Conjunctions on the left can always be decomposed.
          let h34 := h33.left
          let h35 := h33.right
          -- One of the premise coincides with the conclusion.
          exact h25
        case inr h36 =>
          -- Conjunctions on the left can always be decomposed.
          let h37 := h36.left
          let h38 := h36.right
          -- Disjunctions on the left can always be decomposed.
          cases h38
          case inl h39 =>
            -- One of the premise coincides with the conclusion.
            exact h25
          case inr h40 =>
            -- One of the premise coincides with the conclusion.
            exact h25
    case inr h41 =>
      -- One of the premise coincides with the conclusion.
      exact h25
  case inr h42 =>
    -- One of the premise coincides with the conclusion.
    exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314663366060784107998105245320 : (p3 ∨ ((p4 ∧ (True ∧ ((((p5 ∨ p3) ∧ (p1 ∨ ((p2 ∨ p5) ∧ p1))) ∨ p1) ∧ p3))) ∨ ((p3 → (((p5 ∧ p1) ∧ p5) → p3)) ∨ p3))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756482376312165347879260135868 : (((p1 ∧ ((((True ∧ p4) → p1) ∨ (p5 → (True ∧ (p2 → (((p3 → (p4 ∨ p3)) ∧ p2) ∨ False))))) ∧ ((p5 → True) ∧ (p3 ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699682673740048007179401627823 : (((((p1 ∨ (False → (p2 ∧ ((True → p5) → (p3 → p2))))) → False) → (p4 → (False ∨ (p1 ∧ (p1 ∧ (False ∧ (True ∨ (p5 ∧ p1)))))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p1 ∨ (False → (p2 ∧ ((True → p5) → (p3 → p2))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h3
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716391114001984995522164808165 : (((((p5 ∨ p3) ∧ (p5 ∨ p2)) ∧ (p4 → ((p1 → p4) → (False ∨ (((p2 ∧ (False ∨ (False → (p3 → (p5 ∧ False))))) → p1) ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260245237751449019111563595207 : ((p2 → p3) → ((p4 ∧ ((p5 ∧ (p3 ∧ p3)) ∨ ((p3 ∨ False) → p4))) ∨ (((p1 ∧ ((False ∧ (True ∧ False)) → True)) → (False ∧ True)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199428092824151212233119901907 : ((((p3 → p3) → (p3 ∧ (p1 → p1))) ∨ p3) → (p2 → ((True ∧ (p1 ∧ p4)) ∨ (p1 → (((((p4 → False) ∨ p2) ∨ p4) ∨ p3) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337437087652627829048340069775 : (p1 → (((((p1 ∧ p5) → (p1 ∧ False)) ∧ p2) ∧ (p1 ∧ (((True ∨ True) ∨ ((p3 → p5) → p4)) ∧ (p4 ∨ p4)))) → ((True → False) ∨ p2))) := by
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
  let h7 := h4.left
  let h8 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185524526047564873139763822368 : ((p3 ∨ ((False ∨ (p5 → (False ∧ (True ∨ (False ∨ False))))) → p3)) ∨ (p4 ∨ (((((p5 ∨ p3) ∨ (p3 ∨ p1)) ∨ p2) → (True ∨ p5)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167028117753104672484800804250 : ((((((p1 ∧ ((p5 ∧ True) ∨ p3)) → ((p5 ∨ (True ∨ p1)) → p4)) → False) ∧ p4) ∨ False) → ((p4 ∨ p4) ∧ (p1 ∨ (p1 ∨ (p3 ∧ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : ((p1 ∧ ((p5 ∧ True) ∨ p3)) → ((p5 ∨ (True ∨ p1)) → p4)) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h10.left
        let h14 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h18 =>
          -- One of the premise coincides with the conclusion.
          exact h8
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h10.left
          let h22 := h10.right
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h23 =>
            -- Conjunctions on the left can always be decomposed.
            let h24 := h23.left
            let h25 := h23.right
            -- One of the premise coincides with the conclusion.
            exact h8
          case inr h26 =>
            -- One of the premise coincides with the conclusion.
            exact h8
        case inr h27 =>
          -- Conjunctions on the left can always be decomposed.
          let h28 := h10.left
          let h29 := h10.right
          -- Disjunctions on the left can always be decomposed.
          cases h29
          case inl h30 =>
            -- Conjunctions on the left can always be decomposed.
            let h31 := h30.left
            let h32 := h30.right
            -- One of the premise coincides with the conclusion.
            exact h8
          case inr h33 =>
            -- One of the premise coincides with the conclusion.
            exact h8
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h34 := h7 h9
    -- False on the left can always be used.
    apply False.elim h34
  case inr h35 =>
    -- False on the left can always be used.
    apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257573266262038271925845339549 : ((p3 ∨ p1) → (((p4 ∧ ((p5 → (p4 ∧ (p4 → p4))) ∧ p5)) ∧ p5) → (((p5 ∧ ((False ∨ p5) → False)) ∨ p3) ∨ (p5 ∨ (p4 → p2))))) := by
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
  cases h1
  case inl h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39530338162752609036139543975 : (((False ∨ ((p1 ∧ (((p4 ∧ True) → (p1 ∧ p1)) ∨ p4)) ∧ ((False → (p4 → (p4 → ((p4 ∨ (p3 → p4)) → False)))) ∧ False))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178005871990098532049162765975 : (((p3 ∨ ((False ∧ p3) ∧ (p5 ∧ (p3 → (True ∧ (p2 ∨ True)))))) ∨ p3) ∨ (p5 ∨ (((False ∧ True) ∧ p5) → ((True ∨ (False ∧ p5)) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259981504643322029580686543653 : ((p2 → True) → ((False ∨ ((((p1 ∧ p2) ∧ (((p1 ∨ p2) ∨ p2) ∨ p2)) ∧ False) ∧ ((True ∧ (((True ∧ p1) → p4) → True)) ∧ p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204143572368582160000732478422 : ((((p4 → (p1 ∨ p4)) ∧ p1) ∧ p2) ∨ (((((False ∧ (False ∧ (False → (p4 ∨ (True ∨ p4))))) → (p1 ∧ p3)) → p3) ∧ p3) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231901741474922830035221058631 : (((False ∨ True) → p3) → ((((False ∨ (p4 ∨ True)) ∧ (p3 ∧ p1)) ∧ (((p4 ∧ (p2 → ((p4 ∨ p4) ∨ p3))) → True) → (p3 → p5))) → p5)) := by
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
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h6.left
      let h11 := h6.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h12 : ((p4 ∧ (p2 → ((p4 ∨ p4) ∨ p3))) → True) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h14 := h4 h12
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h15 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h16 := h14 h15
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h6.left
      let h19 := h6.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h20 : ((p4 ∧ (p2 → ((p4 ∨ p4) ∨ p3))) → True) := by
        -- Implications on the right can always be decomposed.
        intro h21
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h22 := h4 h20
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h23 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h24 := h22 h23
      -- One of the premise coincides with the conclusion.
      exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181600702623576392691605434026 : ((p1 → (False → (((p5 → (False → p1)) ∧ p5) ∧ (p5 ∧ (p3 ∧ p4))))) → (p3 → (p4 → ((((p1 → p2) ∧ p1) ∨ (p3 → True)) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186732809220035580178919358444 : (((p2 → (p5 ∧ (p2 → (True ∨ p5)))) ∨ ((p2 ∧ False) → p3)) → (p4 ∨ (((p4 ∧ False) ∨ p5) ∨ (False → ((p1 → (p3 ∧ False)) ∧ p5))))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h6
    -- False on the left can always be used.
    apply False.elim h6
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683843528953088975324498473941 : ((((((p4 ∨ p2) ∧ (p2 ∧ ((((False ∧ (p5 ∧ p5)) ∧ p2) ∧ True) ∨ (p1 ∧ p5)))) ∨ p3) ∨ (True ∨ ((p3 → p5) ∨ (True ∨ True)))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_343274491063335131838125869993 : (p2 → ((p2 ∧ True) ∧ (p5 ∨ ((True → ((p3 → (p4 → p2)) → ((p2 → True) → (p5 → p1)))) ∨ ((True ∨ (False ∨ (False ∧ True))) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676082791140175310545935791384 : (((((((p1 ∨ (p5 ∨ p4)) ∨ p5) ∧ p1) → (((False → p4) → ((False ∨ True) ∨ (True ∨ p3))) ∧ p5)) ∧ (p1 ∧ (p5 ∨ (p1 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48216399715758206355233125665 : ((((p1 → True) → ((((p4 ∨ ((p2 → p1) ∧ p2)) → (p5 ∧ ((p2 ∧ p1) ∧ p4))) → False) ∨ (True ∨ (p4 ∧ p3)))) → (p3 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309790490735940942524074496687 : (p2 ∨ ((((False ∨ ((p5 ∨ p1) ∨ (True ∨ ((p2 ∧ ((p5 → p2) ∨ p4)) ∨ p3)))) → p2) ∧ (p4 → False)) ∨ (True ∨ ((p5 ∨ True) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234609869787833466874477195407 : ((p3 → (p5 ∨ False)) → ((p1 ∨ (((p1 ∨ ((p2 ∨ p1) ∨ p1)) ∧ (p4 ∧ p3)) ∨ True)) ∨ (p4 ∧ (((p1 ∨ True) → p2) ∨ (True → True))))) := by
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
theorem thm_5_vars_223411132643082816519157823291 : ((True ∨ (p1 → p3)) ∧ ((p5 → (p5 ∨ True)) ∧ (((True ∨ (((True ∧ p3) → (p1 ∨ p1)) → p2)) → ((p1 ∨ True) → p3)) ∨ (p4 → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260525116674332544599797266604 : ((p3 → p1) → ((((((p4 ∨ ((p4 → (True ∧ p5)) ∧ (p4 ∧ p5))) ∨ True) ∧ (p2 → (p3 ∧ (True ∨ p3)))) ∧ p5) ∨ (False → p2)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262193794905687571478376715723 : (True ∧ ((((((((p1 ∧ (p3 ∨ p1)) → p4) ∨ (p1 ∧ p2)) ∨ True) → True) ∧ ((p4 → ((p1 → (p2 → True)) ∨ p1)) ∨ p3)) → False) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105768761074526422964011245738 : (((((((((p1 → True) → p2) → True) ∧ p3) ∧ ((True ∨ False) → False)) → p2) ∧ p1) → (((p2 ∨ p2) ∨ p1) ∨ (p4 ∧ p1))) ∧ (False ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171297160686229899705260248516 : (((((((True ∨ (p2 ∧ p3)) ∧ (p4 ∨ (True ∧ p3))) → p5) → p3) ∧ p5) ∧ p2) ∨ (False → (((p2 ∧ ((p3 ∨ False) → p1)) ∨ p5) ∧ p3))) := by
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
theorem thm_5_vars_645415882481371385066683009338 : ((((p4 ∨ ((False ∨ (((p2 ∧ (p3 → p4)) → ((p5 ∧ True) → False)) ∧ ((p5 ∧ p3) ∨ p5))) → (((p1 → p5) → p5) → p3))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205609128858414474017652571837 : (((True ∧ p2) ∨ (p1 ∧ (p1 ∧ p2))) ∨ ((p1 ∧ (p3 → ((p3 → (((p2 ∧ True) ∨ p3) → p2)) → (p5 → True)))) ∨ (True → (p1 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56070014691105089319065769971 : ((((p2 ∧ (p1 ∨ p2)) → False) ∨ (p1 ∧ (((True ∧ ((p2 ∧ p5) ∧ (p2 ∨ p4))) → (((p1 ∧ p4) ∧ True) ∧ False)) → (p2 ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354101376785560392413363059183 : (p4 → (p5 → ((((False ∧ False) ∧ ((False ∧ p3) ∨ ((True ∧ p1) → p3))) ∧ p3) ∨ ((True ∧ ((p3 ∧ (True → (p2 → p4))) → p4)) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_390703560940311862861407406617 : (((((True ∧ ((p4 → True) → (p4 ∧ (True → False)))) ∨ (((p1 ∨ ((p2 ∧ p4) → (p1 ∨ (True ∧ p4)))) ∧ p1) ∧ (True ∧ p4))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_310693204133969009731414223558 : (p2 ∨ ((p1 → (False ∧ (p1 ∧ p4))) → (((p1 ∧ (p2 ∨ (((p2 → p3) → (p3 ∧ (False → p4))) ∧ ((p4 ∧ True) ∨ p5)))) ∧ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250930278969952699171822716948 : ((p1 → p4) ∨ (((True → (((p3 ∨ p2) ∨ ((False ∧ (p5 ∧ p2)) ∨ p1)) ∨ ((p3 ∨ (p4 → True)) ∨ p3))) ∨ (p1 → (p1 ∧ p2))) ∨ p5)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623733195739381526386510824811 : ((((p1 ∨ ((((p4 → p4) ∧ (((((p1 → False) ∧ p4) ∧ (p2 → p2)) ∨ p1) → (p4 ∨ p5))) ∨ (p2 ∨ p5)) → (p1 ∨ p1))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179446236968171594139648064938 : ((p5 ∨ (((p1 → p5) ∨ (((p3 → p3) ∨ (p2 ∨ True)) ∨ p4)) → p2)) ∨ ((p4 ∨ (p2 ∧ (p4 → p2))) → (False → ((p3 → True) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226520638970241739756285901500 : (((p3 → p1) ∨ p3) ∨ ((((True → ((p4 ∨ p2) ∨ p5)) → False) ∨ True) ∧ (p2 → (p5 → ((p4 ∧ p4) → ((p3 ∧ (p2 ∧ True)) → True)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66662812666650858833405351492 : ((True → ((((p1 ∨ p1) ∨ (False ∨ p5)) ∧ p5) ∧ ((p2 ∧ (((True ∨ p1) → p4) ∧ ((p5 → (p2 → p2)) ∧ (p3 ∧ p5)))) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149082158487812256078953421689 : ((((p1 → p2) → p5) → ((((False → p2) ∨ p2) → False) ∨ ((((p4 → p4) ∧ p3) → False) ∨ (False → p2)))) ∨ ((p5 → p4) ∧ (p2 → p1))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310030557975954968883094122787 : (p2 ∨ ((((p1 ∧ (p3 ∨ False)) ∧ (p2 ∨ True)) ∧ (True ∨ (p1 ∨ ((True → p3) ∧ p4)))) ∨ ((((p4 ∨ p4) ∨ False) → (p1 ∨ True)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330752345228581038796641347605 : (True → (p1 → (((False → p5) → p4) → (((((p4 ∧ p3) ∧ ((p4 → (((True ∧ False) ∨ p1) ∨ p3)) → p2)) ∧ p5) ∨ (p4 → p5)) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (False → p5) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49136392391373046675395392803 : (((((False ∧ (p2 ∧ ((p3 ∧ True) ∧ p2))) ∧ (p1 → p1)) ∧ (p3 ∧ (p2 ∨ (p3 → (p1 ∨ (p1 ∨ p5)))))) ∨ (p1 → (p3 → p3))) ∨ p1) := by
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
theorem thm_5_vars_68068829811580592249261316254 : ((p2 → (p1 ∨ (p3 ∧ ((((p5 ∧ True) → ((p4 → (p5 ∧ ((p1 → p5) ∨ (p2 ∨ p1)))) → p4)) ∧ p3) → ((False ∨ p5) ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138019676626273090385915738304 : ((True → (((p1 → ((p4 ∨ (p3 ∨ p2)) ∧ (p2 ∨ ((((p2 → (p3 ∨ True)) → p2) ∧ p1) ∧ True)))) ∧ p5) → p4)) ∨ (True ∨ (p4 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_830734995804364874291067978734 : ((((True → ((p1 ∧ (((p3 ∨ (False ∨ True)) ∨ ((((True ∨ p1) → (True ∧ True)) ∧ p4) ∨ (False ∨ (p1 → False)))) ∨ p5)) ∧ p5)) ∧ p4) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148089339148258637057133480169 : (((((p2 ∧ (((False ∧ p3) ∨ (p3 ∧ (p1 → (p1 ∨ (True → True))))) ∨ False)) → False) → p2) → (False ∧ p2)) ∨ (False → (p2 ∨ (p3 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197021551883585279911735283761 : ((((p1 ∨ (p5 ∨ p3)) ∨ (p4 ∨ p5)) ∨ p3) ∨ (True ∨ ((p5 ∨ p2) → (((((p3 ∨ p1) ∧ ((p1 ∨ p5) ∨ p4)) ∧ p4) → True) ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340848053581251124579346111733 : (p2 → (((((True ∧ ((False → (p3 ∧ ((p2 ∧ (p5 ∧ (p3 ∨ p1))) ∧ True))) ∨ False)) ∧ p3) → (p4 ∧ p3)) ∨ ((p2 ∨ False) → True)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64560087715991014303190728960 : ((p1 ∨ ((True ∨ (False ∧ (p1 ∨ p3))) → (p3 ∧ (((p4 ∧ p1) ∧ (((p1 ∧ True) ∨ (((p2 ∧ p1) ∨ False) ∧ p2)) ∧ True)) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306682218315995818361165047110 : (p1 ∨ (True ∧ (True → ((((True ∧ (p3 ∨ (p3 ∧ False))) ∨ (p1 ∨ (p2 → (True → (True ∨ p2))))) ∧ False) ∨ (False → ((p3 → p5) ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174817501528611466245844853936 : (((p4 → p5) ∧ (((p3 ∨ (p3 → True)) → (p1 ∧ p3)) → (p4 → (p3 ∧ p4)))) → (((p4 ∧ p4) → p5) ∨ ((p4 → (p2 → p1)) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173487294216620498950570112921 : (((((((p1 → p4) → p5) ∧ True) → (p2 ∨ (p1 ∨ (True ∨ p3)))) → False) ∧ p3) → (((p4 ∧ p4) → p1) ∨ ((p4 ∨ (p4 → p4)) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149227125054634252964521856197 : (((p4 ∧ True) ∨ ((True ∧ (p2 ∨ ((p5 → p4) ∧ p4))) ∧ (p3 ∧ ((p1 ∨ False) → (p1 ∨ (p3 ∨ p1)))))) ∨ (((p1 → p3) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_995087474252991019167423269806 : (((p5 ∧ ((p5 → (False ∧ ((p1 ∨ p1) ∧ (p2 → (((p3 → False) ∨ p2) ∧ True))))) ∧ (((p2 ∨ p3) ∨ ((p1 ∨ p5) ∨ p3)) ∨ p3))) → False) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h9 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h10 := h4 h9
        -- We need to get the left conjuct of h10 based on <expert-advice>.
        let h11 := h10.left
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h13 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h14 := h4 h13
        -- We need to get the left conjuct of h14 based on <expert-advice>.
        let h15 := h14.left
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h19 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h2
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h20 := h4 h19
          -- We need to get the left conjuct of h20 based on <expert-advice>.
          let h21 := h20.left
          -- False on the left can always be used.
          apply False.elim h21
        case inr h22 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h23 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h22
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h24 := h4 h23
          -- We need to get the left conjuct of h24 based on <expert-advice>.
          let h25 := h24.left
          -- False on the left can always be used.
          apply False.elim h25
      case inr h26 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h27 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h28 := h4 h27
        -- We need to get the left conjuct of h28 based on <expert-advice>.
        let h29 := h28.left
        -- False on the left can always be used.
        apply False.elim h29
  case inr h30 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h31 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h32 := h4 h31
    -- We need to get the left conjuct of h32 based on <expert-advice>.
    let h33 := h32.left
    -- False on the left can always be used.
    apply False.elim h33
  -- True on the right can always be proven directly.
  apply True.intro



