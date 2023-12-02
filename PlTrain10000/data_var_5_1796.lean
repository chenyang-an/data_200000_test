variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177861037458837067460166612043 : ((((((p4 → False) ∨ p5) ∧ (True → ((False ∧ p5) ∨ p3))) ∨ p2) ∨ True) ∨ ((((p2 ∧ p2) ∧ (p2 → p5)) → (True → p1)) → (False ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667658726634310113854079876059 : ((((p3 ∧ ((p5 → (p1 ∧ (True ∨ p4))) → ((((p2 → True) ∨ True) ∧ (((p2 → False) ∨ p1) ∨ p2)) ∨ p2))) ∧ ((True → p3) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114939052443901427177611835681 : ((((p4 ∨ (p5 ∨ (p3 → False))) ∨ ((((p1 ∨ p4) ∨ p5) ∧ p2) ∨ p4)) → (p5 ∧ (((p5 → p2) → (p5 → p5)) ∨ False))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618878647482280140775012644941 : (((((True → (p1 ∧ p1)) ∧ (p3 ∧ (p3 ∧ (False ∧ ((((True ∨ p5) ∧ (True → (p2 ∨ False))) → p4) → (p5 → (False ∧ p1))))))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_356066455209118021629377276901 : (p5 → (((p5 ∧ (p4 ∧ (((False → p3) → (p1 → (((False ∨ p5) ∧ p4) ∧ p1))) ∨ (False ∨ p4)))) → True) → (((True → p4) ∧ p3) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156715920493940160408892709334 : ((((False → ((True ∨ p3) → (p1 ∧ (False ∧ p3)))) ∧ (((p3 ∨ (p5 ∨ p1)) ∨ False) → p2)) ∧ p3) ∨ ((p5 ∨ ((False → p2) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308473065043403262316222811906 : (p2 ∨ (((((p4 → (p4 ∨ ((p4 ∨ p3) → p3))) ∨ p3) → (((p4 → ((True ∨ False) ∧ (p4 ∨ p5))) ∧ p3) ∨ p3)) → (p1 ∨ p3)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 → (p4 ∨ ((p4 ∨ p3) → p3))) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225850185191070530329995340256 : (((False ∧ p1) ∨ p1) ∨ (p4 ∨ (p1 ∨ (False → (((p3 → p1) ∨ ((p2 → False) ∧ (((p3 ∧ p4) ∨ (True → (p2 ∧ p4))) ∧ p4))) → True))))) := by
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
theorem thm_5_vars_178566476959607967814462259053 : ((((p5 → p1) ∧ (False ∧ (False ∨ False))) ∧ ((p1 ∧ p2) → (p5 ∧ p1))) ∨ ((((p2 ∨ p3) ∧ p3) → ((p4 ∧ True) → p3)) ∨ (False ∨ False))) := by
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
  let h5 := h1.left
  let h6 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56343061257125117066077501312 : (((((False ∧ p1) → False) ∨ p4) → (((p5 ∨ True) → ((p3 ∨ p5) ∨ ((p3 → True) ∨ ((False ∧ p2) ∧ p3)))) ∧ (True ∧ (False → p5)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h11
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158527740682689046683431336745 : (((p5 ∨ p4) → ((p3 ∨ (True → (p5 ∨ True))) ∧ ((((False → p3) ∧ (p1 ∨ p1)) ∧ False) ∧ True))) ∨ ((p4 ∧ p5) → ((p2 → p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172517061604055159160500677556 : ((((p1 → False) → p4) ∧ (True → ((p1 ∧ (p3 ∨ (p2 ∨ (True ∨ p2)))) ∧ p1))) ∨ ((p5 → (False ∧ (p4 ∨ (False ∧ p2)))) → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66173566546094759256143864778 : ((p5 ∨ (((((p2 ∨ False) ∨ p5) ∨ p4) → (((False → (((p4 → False) ∨ True) ∨ p4)) → p2) → (p3 ∨ p5))) → ((p2 ∨ p1) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165598075130732963651476156090 : (((((p4 → (True → p2)) → (p2 → p1)) → p4) → ((p4 ∨ (p2 → (p5 ∧ False))) ∧ p5)) ∨ (False → (p5 ∨ (p5 → ((p4 → True) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724783797860110132668961503528 : ((((p3 ∨ (p4 → p1)) ∧ (((p5 → p2) → ((p5 → (True → p4)) → (p5 → (((p5 ∧ p4) ∧ p3) → ((p5 ∧ p4) → p2))))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62699274991996939113248428711 : ((p4 ∧ (((((p1 → p2) → (True → (p1 ∨ (p5 ∨ p2)))) → (True → (p1 → (p1 → (p1 → False))))) ∨ (p3 ∨ (True → p3))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340957100283885319102507368180 : (p2 → ((((p1 → p4) ∧ p4) → (((p3 ∧ ((p1 ∨ (p5 → p4)) → True)) ∨ (p4 ∧ ((p4 ∧ p2) ∨ False))) → (False ∧ (p3 ∨ p2)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650006271374182590962288681599 : (((((p1 ∧ (p2 ∧ ((p5 → p2) → (p3 ∨ (p1 ∨ (p4 ∨ ((True → p5) ∨ (p3 ∧ p3)))))))) ∨ ((p5 → p3) ∨ p4)) ∧ (p5 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106492019823227452389267439420 : (((((True → p1) ∧ (False ∧ (p3 ∧ p5))) ∧ p4) ∨ ((p2 ∨ (((False ∧ p5) ∧ False) → (True ∨ ((p4 ∨ p4) ∨ True)))) ∧ True)) ∧ (p3 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164089576721025389181372257915 : ((p2 ∨ ((True → (((False ∧ (p3 → (True ∨ (p1 ∧ p4)))) ∨ p5) ∧ (True → p1))) ∨ True)) ∧ ((True → True) ∨ ((p2 ∧ p3) ∧ (False ∨ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110896248580627956040543814019 : ((((((p5 → False) → False) ∧ (False → ((False ∧ (p5 ∧ ((((p4 ∧ p5) ∧ (False ∧ True)) → p4) → p5))) → p2))) → p2) ∧ False) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670317248751143300029349567605 : (((((p3 ∧ (p5 → True)) ∧ (True ∧ (p5 → (((p4 ∧ True) ∧ (p3 ∨ p3)) ∧ ((p2 → p5) ∨ (p1 ∧ p3)))))) ∨ ((p3 → False) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200901717052023642297501910800 : ((False ∨ (True → ((p4 ∧ p4) ∨ (p5 ∧ False)))) → (((p1 ∨ ((p4 → ((p1 → p5) ∨ p4)) → p2)) ∨ p1) ∨ ((p1 → p3) → (p5 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184757205598132801762654548302 : (((False ∧ (p5 ∧ (p4 → False))) ∧ (p1 ∧ (True ∨ (False → p5)))) ∨ (((p2 ∨ ((False ∨ (((p4 → p5) → p3) ∨ False)) → p1)) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684721278206328964703751322989 : (((((False ∨ p3) ∧ ((p3 → ((p5 → p2) ∨ ((True ∧ False) ∨ (p3 → p5)))) → (p2 → p2))) ∨ ((True ∨ p5) ∨ (False ∨ (p5 → p3)))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702374347539634437452321719994 : ((((((p1 ∨ (((False ∧ False) → p3) ∨ p2)) → p3) ∨ p1) ∨ ((p1 ∨ False) → ((((p5 → p1) → (p1 ∧ p1)) → (p4 ∨ p5)) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208497027546453291894708435614 : (((p1 ∧ True) → (True ∨ (p4 ∧ p4))) → ((p2 → (False ∧ (p2 ∧ p5))) ∨ (p2 ∨ (True ∨ ((p2 ∨ p5) → (p3 ∧ ((p3 ∨ True) ∧ p1))))))) := by
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
theorem thm_5_vars_758237436834147047939459783786 : (((p1 ∧ (p5 → ((p3 → p1) ∧ ((p3 ∨ ((p4 ∧ (True ∨ ((((p3 ∨ (True ∨ (p5 ∨ p2))) → p4) → False) → False))) ∧ p2)) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950194467618543304931605154141 : (((((p5 ∨ False) → p4) ∧ (p4 ∧ (((((p4 ∧ (p1 → p5)) ∧ p3) ∨ ((p5 ∧ p2) ∧ False)) → True) → ((p3 → (p2 ∧ p1)) ∧ False)))) → p3) ∧ True) := by
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
  have h6 : ((((p4 ∧ (p1 → p5)) ∧ p3) ∨ ((p5 ∧ p2) ∧ False)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_576774101947650611072986233645 : (((p3 → (((p2 → (p1 → ((p5 ∧ False) ∨ ((True ∨ p3) → False)))) → (p4 ∧ ((True → ((p5 → p4) → False)) ∨ (p2 ∨ p2)))) ∨ p3)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215200368935860541707377048738 : ((True ∧ (p2 ∨ (p3 ∨ p5))) ∨ ((p5 → ((p3 ∧ p4) → ((p3 ∧ (p4 ∨ True)) → False))) ∨ ((p4 ∧ p4) ∨ (True ∨ ((p2 ∧ True) ∨ p4))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693851278214354920069599066073 : ((((((p4 ∧ False) → (((((p5 ∧ p4) → True) ∨ p5) ∨ p4) → True)) → False) ∨ ((p2 → (((p4 ∨ p1) → (False ∧ True)) → True)) ∨ p5)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616753286948017025199860067685 : ((((((p5 ∧ (p2 ∧ p1)) ∧ (p2 ∨ (False ∧ (p3 ∨ False)))) ∨ ((p3 ∨ ((p4 ∧ (p1 → (True ∨ p4))) ∨ (p3 → True))) ∨ p5)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329729949024110956133510073626 : (True → ((p3 → p4) → (p4 → ((((p2 ∨ p4) ∧ p5) ∧ p3) ∨ (((((False → (p2 → p3)) → p1) ∨ p2) ∧ p1) ∨ ((False ∧ False) ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106367467609151448094099748604 : ((((((p1 ∨ (p4 → True)) ∨ p1) ∨ (p4 ∨ False)) ∨ p5) → (((p3 → (p2 ∨ p2)) → (((p5 ∨ p2) ∧ False) ∨ True)) ∨ True)) ∧ (True ∨ False)) := by
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56453662905016723020797677877 : ((((False → p5) ∨ (p1 → p1)) → (p1 ∧ (((p4 ∧ (p4 ∧ (p4 ∧ (p5 → (p5 → p1))))) ∨ ((p5 ∨ p4) ∧ p5)) → (p1 ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172508927236591659715981099015 : ((((p2 ∨ p4) ∨ p4) ∧ ((False ∨ p2) → (p4 → (((p2 → p4) ∨ p5) → p2)))) ∨ (((((p5 ∨ p5) → p4) ∨ p5) → (p1 ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695015940511803891351535804724 : ((((((p3 ∨ (True → p4)) → ((((p1 ∧ True) → p5) ∧ False) → p2)) ∧ True) → (p3 ∨ (p4 ∧ ((p1 → (p2 ∧ (p4 → p3))) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780191749546301238310912829459 : (((p2 ∨ (((((((True ∨ (((p5 → p1) → (False → (p4 → False))) ∨ True)) ∨ p1) ∧ False) ∨ p5) → False) → p4) ∨ ((True ∧ False) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255728334835467018997997397978 : ((True ∨ True) → ((((False → True) ∨ ((False ∧ (p3 ∨ ((True ∨ (p2 → False)) → p1))) ∧ p3)) → (p5 ∨ (((p4 → p5) ∧ True) ∧ False))) ∨ True)) := by
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
theorem thm_5_vars_166781077661350735215653681835 : ((p5 → ((p1 → (p1 ∨ (p2 ∧ p2))) → (p1 ∧ ((((p2 ∨ True) ∨ p4) ∧ p5) ∨ p1)))) ∨ ((False ∨ (True ∨ False)) ∨ (p3 ∧ (p3 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41974876578928157752665580376 : ((((p1 ∨ p3) ∧ (((p4 → p1) ∨ False) → (p4 ∨ ((((False → (p2 ∧ p1)) → (True ∨ False)) → (p5 ∧ False)) ∨ (p4 → p5))))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729628885578004934453773705087 : (((((True → False) ∨ False) → ((p2 ∨ (p4 → ((False ∧ p1) ∨ (False ∨ (False ∧ (((((p1 ∧ p4) ∨ True) ∧ p5) ∧ p4) ∨ p4)))))) ∧ p1)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356276853760896461965966974782 : (p5 → ((p4 → ((((p2 → p3) → ((False ∨ p5) ∧ (p2 ∧ False))) ∨ (p2 ∨ False)) ∧ True)) ∨ ((p4 → (False → (p2 → (p5 ∨ p5)))) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238722828920089904655744591749 : ((p1 ∨ True) ∧ ((((p5 → p5) ∧ (((((p4 ∧ False) ∧ p4) ∧ ((False ∨ p1) ∧ p5)) → p5) → (True → ((p5 → p1) → p2)))) → p5) ∨ True)) := by
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
theorem thm_5_vars_156913087413779205851564399733 : (((((p5 ∧ (((p1 → (p4 → True)) ∧ (p2 ∨ (p2 → p2))) ∧ p5)) → (p2 ∧ p5)) → p5) ∨ True) ∨ (True ∨ ((p1 → (p1 → False)) ∧ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138053234979704054024241079615 : ((True → ((p2 ∨ p4) → (((p4 ∨ (p3 ∨ False)) → p1) ∧ (p1 → (False ∧ (p3 ∨ ((p3 ∨ (p5 → p4)) ∧ p3))))))) ∨ ((p4 → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234285523381163337694212982662 : ((False → (p3 → p2)) → ((False → False) → ((p3 → (((p1 → ((p1 → (p2 ∧ True)) ∨ ((p4 ∧ p5) ∧ False))) ∨ (p3 → True)) ∨ p5)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149385586389985593758860685115 : (((p4 → p3) → (p5 ∧ (((((p4 → (False ∨ p5)) → (p3 → p1)) → p5) → (p3 ∨ (p4 → p3))) ∨ p2))) ∨ (True ∨ ((True → p3) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123975226022370003356807026712 : ((((((p1 ∧ (((p2 → True) → p2) → p3)) → p2) → False) → False) ∨ (p3 ∨ (((p3 ∧ (p2 ∧ (p3 ∧ p5))) ∨ False) → p2))) → (p3 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609227723008980222278657355452 : (((((((p3 ∧ p1) ∨ p3) ∨ (((((p4 ∨ p4) ∨ (((False ∧ p4) → False) ∨ False)) ∧ (p2 ∨ (p4 ∨ p1))) ∧ p4) ∨ False)) ∨ p2) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_194715471539171120290686020305 : ((((p5 ∨ p1) → ((p3 ∨ False) ∨ p2)) ∨ True) ∧ ((False ∧ p5) → ((p3 ∨ ((p3 ∧ False) ∨ (((p1 ∨ p4) ∧ p1) → (False → p4)))) → False))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h1.left
      let h12 := h1.right
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149283052588619194798906421831 : (((p2 → p3) ∨ ((((p2 ∨ (p2 ∧ p4)) ∨ (p4 ∧ p2)) → p3) → (((True → (True ∧ True)) → p3) → p3))) ∨ (((p3 → p2) ∨ p3) ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True → (True ∧ True)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197320258801645833495982547346 : ((((True → p4) ∨ (p5 ∧ (p4 → p2))) → p3) ∨ ((p4 ∧ (p1 ∨ ((p3 ∧ p2) → ((p3 ∨ p3) → p1)))) → ((p5 → p4) ∨ (p1 ∧ p5)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258761650972192906656839998106 : ((True → False) → ((p5 ∨ ((((((p2 ∨ ((p1 → (p2 ∧ p2)) ∧ p4)) ∨ p1) → (p5 ∧ p1)) ∧ True) ∧ (p5 → p2)) ∨ (p1 ∧ p3))) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46733439284846889319215832242 : (((True → (p4 → ((((p2 ∧ p2) ∧ (p4 ∧ p3)) → p4) → ((False ∨ (((True ∧ p4) ∧ p2) → (False ∨ False))) ∧ p4)))) ∧ (False → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804404326086334443538515313692 : (((p3 → ((((p2 ∨ (p4 → p1)) ∧ (True → p3)) → (p3 ∧ p2)) ∨ ((p2 ∨ p3) ∨ (((p4 → (True → p4)) ∧ p3) ∨ (True → True))))) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355848828258384706662278401733 : (p5 → ((((((p5 ∨ p2) ∧ (p5 ∧ (p3 → (p5 → False)))) ∨ (((p3 ∨ False) ∨ p4) ∧ p3)) ∧ p1) ∨ (True ∨ p2)) ∨ ((True ∧ p2) ∧ p3))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9893990387805118764226552488 : (((p1 ∧ (((((p3 → p1) → False) ∨ p3) ∨ (p1 ∨ (False ∧ ((p5 ∨ ((p4 ∧ False) → p2)) → ((p3 → p4) → p3))))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156610033733768533621571865974 : ((((p1 ∧ ((((p2 ∨ (((p2 → p5) → p5) → (True ∨ p4))) → p4) ∧ p1) ∨ p2)) ∧ p4) ∧ p4) ∨ (p4 → ((p4 ∧ (p2 → p5)) → p4))) := by
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
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627850063872622999296341139015 : (((((((p5 ∨ p2) ∧ (p4 ∨ ((p2 ∧ (p2 → (p1 → p5))) → p1))) ∧ (p3 → (p3 → (p5 → ((p5 → p3) → p4))))) ∧ p3) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238014365566271681114766548801 : ((True ∨ p1) ∧ (((((True → (False ∧ False)) ∧ (p1 ∧ ((p4 → p5) ∧ (p3 ∨ p2)))) → False) → False) → ((p2 → p1) ∨ (p2 → (p5 ∧ p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True → (False ∧ False)) ∧ (p1 ∧ ((p4 → p5) ∧ (p3 ∨ p2)))) → False) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h12 := h4 h11
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h16 := h4 h15
      -- We need to get the left conjuct of h16 based on <expert-advice>.
      let h17 := h16.left
      -- False on the left can always be used.
      apply False.elim h17
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h18 := h1 h2
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65885755209490220796651190156 : ((p4 ∨ ((p1 → True) → (p5 → (p3 ∧ (p5 ∧ ((p5 → ((p3 ∧ (p1 ∨ True)) ∧ (p4 → True))) ∧ (p5 ∧ ((p1 ∨ p5) ∧ True)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245274181556393723166185631899 : ((p2 ∧ p1) ∨ (p5 → ((p2 ∧ (p5 ∧ ((p1 → True) → (((p4 ∨ (p2 ∧ True)) ∨ p4) → p1)))) → ((p3 ∨ False) ∨ (p1 ∨ (p2 ∨ p5)))))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800095162941636244272986253949 : (((p2 → (((True ∧ False) ∨ ((p3 ∨ p5) ∨ (p3 ∧ ((p1 → (True ∨ (p5 ∧ False))) ∨ (p2 → ((True ∨ p4) ∧ (p5 → True))))))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199011974899406405319226542877 : (((((p4 → (p5 ∨ p2)) → False) ∧ p2) ∧ p2) → (((p3 ∨ p1) ∧ (True ∧ (((((True ∧ p4) → p4) ∨ p2) ∧ (p3 ∨ p3)) → p5))) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p4 → (p5 ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h1.left
      let h15 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h14.left
      let h17 := h14.right
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h18 : (p4 → (p5 ∨ p2)) := by
        -- Implications on the right can always be decomposed.
        intro h19
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h20 := h16 h18
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h1.left
      let h23 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h22.left
      let h25 := h22.right
      -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
      have h26 : (p4 → (p5 ∨ p2)) := by
        -- Implications on the right can always be decomposed.
        intro h27
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h23
      -- We have shown the premise of h24, we can now drive its conclusion.
      let h28 := h24 h26
      -- False on the left can always be used.
      apply False.elim h28
  case inr h29 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h1.left
      let h32 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h33 := h31.left
      let h34 := h31.right
      -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
      have h35 : (p4 → (p5 ∨ p2)) := by
        -- Implications on the right can always be decomposed.
        intro h36
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h32
      -- We have shown the premise of h33, we can now drive its conclusion.
      let h37 := h33 h35
      -- False on the left can always be used.
      apply False.elim h37
    case inr h38 =>
      -- Conjunctions on the left can always be decomposed.
      let h39 := h1.left
      let h40 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h41 := h39.left
      let h42 := h39.right
      -- We want to use the implication h41 based on <expert-advice>. So we show its premise.
      have h43 : (p4 → (p5 ∨ p2)) := by
        -- Implications on the right can always be decomposed.
        intro h44
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h40
      -- We have shown the premise of h41, we can now drive its conclusion.
      let h45 := h41 h43
      -- False on the left can always be used.
      apply False.elim h45
  -- Conjunctions on the left can always be decomposed.
  let h46 := h1.left
  let h47 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h48 := h46.left
  let h49 := h46.right
  -- We want to use the implication h48 based on <expert-advice>. So we show its premise.
  have h50 : (p4 → (p5 ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h51
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h47
  -- We have shown the premise of h48, we can now drive its conclusion.
  let h52 := h48 h50
  -- False on the left can always be used.
  apply False.elim h52



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60020836174412110196890795748 : (((p1 ∨ p1) → (((((False ∧ p4) → ((p3 ∧ p3) ∨ True)) ∧ p3) ∧ ((p4 ∧ p2) → ((p2 → True) ∧ (p2 → False)))) → (p2 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810784122143620289888941723978 : (((p5 → ((True ∨ p3) ∧ (((p2 ∧ (p4 ∨ (((p5 ∧ p4) → True) ∧ ((((p4 ∨ p3) ∧ (p2 ∧ p3)) ∧ p3) ∨ p1)))) ∧ p2) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117091221086815389581419601468 : (((p1 → False) → (True → ((((p4 ∨ False) ∨ p5) ∨ p2) → ((p1 ∨ ((p4 ∧ (p3 ∨ ((p4 ∨ p2) → False))) ∨ p1)) → p3)))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46114879654436686697885066646 : ((((False ∨ (p2 ∨ (True ∧ (((True ∧ False) ∧ p1) ∨ (True → ((p2 ∧ (p1 ∧ p4)) ∨ ((p1 ∧ p1) ∨ p1))))))) ∨ False) ∧ (p3 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184628974015346252729201361518 : (((p1 ∧ ((p1 → p5) ∨ (p1 ∨ False))) ∧ (False ∨ (False ∧ p3))) ∨ ((((True ∨ p5) ∨ p5) → (p1 → False)) → ((p5 ∨ (True ∨ True)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_116407654427025563896563193149 : (((True ∨ (False → p1)) → (p5 → (p4 ∨ ((p1 ∨ (((p5 ∧ False) ∨ ((p5 ∨ p1) → p1)) → ((p3 → p2) ∨ False))) → p1)))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136338075035930215245323493240 : (((p2 ∧ (p4 ∧ (p5 → p5))) ∧ (((p3 ∨ p4) → False) ∧ ((((p2 ∨ True) → p5) → (False ∧ False)) → (p1 → p4)))) ∨ ((p2 → p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126809932985543570045784871926 : ((p5 ∧ ((p5 ∧ (((True ∧ ((p4 ∨ p1) → (p4 ∧ (p5 → (p5 → (((p1 → p3) → True) → False)))))) ∨ True) ∧ True)) → False)) → (p3 ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p5 ∧ (((True ∧ ((p4 ∨ p1) → (p4 ∧ (p5 → (p5 → (((p1 → p3) → True) → False)))))) ∨ True) ∧ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345677896062502875935862563923 : (p3 → ((p2 ∨ ((p2 ∨ (p4 → (False → (p5 ∧ p5)))) ∧ (p4 → ((p2 ∨ False) ∨ ((p4 ∧ ((p3 ∨ False) ∧ (p1 ∨ p1))) ∧ p2))))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589792943995760414834946753354 : (((((((True ∨ ((((((p4 → (p4 ∨ (p3 → False))) → p1) ∧ True) ∨ p1) ∧ (p5 ∧ False)) ∧ p2)) ∨ p1) → (p5 → p3)) → p1) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962574781379305722961098243709 : ((((True → p4) ∧ ((False ∧ p5) ∨ (p5 ∧ (((p2 ∨ ((p2 ∨ p2) → p3)) ∧ p3) → (((p4 ∨ p3) ∨ p3) ∧ ((p2 ∧ p4) ∧ p4)))))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184420760325542243162653481530 : (((((False ∧ (p2 ∧ p3)) ∨ p4) ∧ (p3 → p4)) ∧ (p3 ∧ p2)) ∨ ((((False → p2) ∧ ((p1 ∧ True) ∧ p3)) → (p2 → (p2 ∨ p1))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115481902475280768539838083617 : (((p5 → (p5 ∧ (p4 → ((p2 ∨ True) ∧ False)))) ∨ (((p5 ∨ ((p1 → p5) → ((p2 ∨ p5) ∧ p3))) ∨ (False ∧ p2)) ∧ p2)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55379564690799487745265719998 : (((((p3 ∧ (p2 ∨ p5)) → p5) ∧ p2) → (p2 → (((p3 ∨ p4) → p2) ∧ ((p4 ∨ (p2 ∨ (((p4 ∨ p2) → True) ∨ p4))) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599045208711866050232775207223 : (((((p5 ∨ True) ∧ ((p5 ∨ (((False ∧ p3) ∧ p3) ∨ p1)) ∨ (p5 ∨ (((False → (p1 ∧ ((p3 → p5) → p1))) ∧ False) → p1)))) ∧ True) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696227270382137142452566948094 : ((((p4 ∨ (True ∨ (((p2 ∧ True) ∧ True) ∧ (((p3 → True) ∧ False) ∧ p5)))) → ((((False ∨ ((p2 ∧ p2) → p1)) ∨ p5) ∧ p4) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263086699991321409461458097361 : (True ∧ (((p3 → (((p1 → (p5 ∧ p5)) → (p5 ∨ (((False ∧ False) → True) ∧ p1))) ∨ (p4 ∨ (p3 ∧ (p4 → True))))) ∨ True) ∨ (True ∧ p1))) := by
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
theorem thm_5_vars_114183296113321360375710803694 : (((((True ∧ p5) ∨ (((True ∧ p3) ∨ (p2 ∨ (p1 ∧ (True ∨ p1)))) ∧ True)) ∨ (p1 ∧ (False ∧ p4))) → ((p5 → False) ∧ True)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354767842983443590082567465819 : (p5 → ((((p4 → ((True ∨ ((True ∨ p1) ∧ p5)) → (p3 ∧ p5))) ∨ False) → ((p4 ∨ p1) ∨ (p3 ∨ (((p4 ∧ False) ∨ p3) ∧ p5)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3168139105202197515672327738 : ((p5 → True) ∧ (False ∨ ((((p1 → p2) ∨ (((p1 → p4) → p1) → ((p5 → True) → p3))) ∨ (True → ((p5 ∧ False) ∨ True))) ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669261002414495298141458842606 : (((((p5 ∨ (p1 → (((p2 ∧ ((((p2 ∨ False) ∧ (p4 ∧ p3)) ∧ p2) → p4)) ∧ p1) ∧ (p2 ∧ p3)))) → p3) ∨ ((True ∧ p3) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159191834292876241961144770945 : ((p2 → ((p1 ∧ (p1 ∨ ((p4 ∨ ((True → True) ∧ False)) ∨ ((p1 ∨ p4) ∨ (p2 → p3))))) ∧ False)) ∨ (((False ∨ p3) → (p5 ∨ True)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216077063697567019320401232505 : ((True → ((False ∧ False) ∧ True)) ∨ ((p5 ∨ p2) → ((p5 → (True ∧ (p3 → (False ∧ ((p2 ∨ ((p3 ∧ (True → p5)) ∧ p3)) ∨ p2))))) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302879243581365901956795063803 : (False ∨ (True → (((p1 ∧ True) ∧ (((True ∧ p2) → p4) ∨ (False ∨ (True → ((False ∧ (p5 ∧ p2)) ∨ p2))))) ∨ ((True → p1) ∨ (p4 → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_443777264764180409226380114353 : ((((((p1 ∨ False) → p4) ∧ ((True → ((((p3 → False) ∧ (p1 ∧ p3)) → ((p1 ∨ False) ∨ False)) → False)) ∧ False)) ∨ (True → (False → True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135378622507380906269406789495 : ((((p3 ∧ (((p4 ∨ p4) ∧ True) ∧ ((p5 → p2) → ((p1 ∨ p3) ∧ (False → p5))))) ∨ p2) ∨ ((p2 ∨ True) → p4)) ∨ ((p2 ∨ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187359635889615298332771778956 : ((p3 ∧ ((p5 → ((False ∧ ((p2 → p1) ∧ p5)) ∧ True)) ∨ False)) → (((True → (False ∨ False)) ∨ p2) → (p1 ∨ (((p3 ∨ p3) → p2) ∨ p4)))) := by
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
    cases h5
    case inl h6 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h8 := h3 h7
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h16
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h18 =>
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h19 =>
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196363722903233640472619807957 : ((p5 ∨ ((True ∧ (True ∨ False)) → (False → p1))) ∧ (((((p4 ∨ p5) → True) → (p3 ∧ (p5 ∧ (p1 → ((False ∧ p5) ∨ p3))))) ∨ True) ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119546102861403836121178493710 : ((p5 → (((((p2 ∧ p1) → True) ∨ p2) → ((True → (False → True)) ∨ (((p5 ∧ (p3 ∧ p4)) ∨ p2) ∨ p3))) → (p1 ∧ p1))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703586306665755556278391731400 : ((((p3 → ((p4 → p2) ∧ (p2 → ((p5 ∧ p3) ∨ False)))) ∨ (p3 ∧ ((p3 ∧ ((p3 ∨ False) ∧ ((False ∨ (p1 ∧ p3)) → p4))) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150058666124494803482073210446 : ((True → ((p2 → (((p4 → False) → (p4 ∨ p2)) → (True ∧ (p2 ∨ ((p2 ∧ p1) → (p3 → p1)))))) → p4)) ∨ (False → (p5 → (p3 ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148940736064911261117178672511 : (((p2 ∨ ((p5 → p4) ∨ True)) → ((p3 ∨ (p3 ∨ (p3 → p3))) ∨ (p2 ∧ ((p4 ∧ (p2 ∧ False)) ∨ p2)))) ∨ ((p3 ∨ (p4 → True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247853563781488066025357919627 : ((p1 ∨ p2) ∨ (((p1 → (((p2 ∨ False) ∧ p2) ∧ (True ∧ ((True → p4) ∨ p5)))) → False) ∨ (p3 → ((True → (True ∨ False)) ∨ (p1 → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54712367012672671317210595282 : ((((((False → False) ∨ p4) ∧ p1) → (p4 ∨ p1)) → (p4 ∨ ((p1 → (False ∨ (False ∧ ((p3 ∧ p2) ∨ p3)))) ∨ ((p2 ∨ False) → True)))) ∨ False) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



