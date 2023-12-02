variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735964196915642136446030756968 : ((((True → p2) ∧ ((p4 ∧ (p2 ∧ False)) ∧ (((p5 ∨ (p3 → (p2 ∨ (False → False)))) ∨ p2) ∧ (p1 ∨ (p3 ∧ (p1 ∧ (False → p5))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50764110542832765664978832804 : (((True ∨ (True ∨ ((p4 ∨ ((p4 ∧ (p4 ∧ ((((p5 ∨ p5) → p4) ∨ p3) ∧ p4))) ∨ True)) ∨ p2))) → ((p4 ∨ p3) → (p4 → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57916409298530514243691387971 : (((p5 ∨ (False ∨ p1)) → (((p5 → False) → (((p4 ∨ False) → p4) → p4)) ∧ (((True ∧ p3) ∨ p4) ∧ (p1 → (p1 ∨ (p1 ∧ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805427442126270064683381000649 : (((p3 → (p1 ∨ (p1 → ((((p1 ∧ True) → False) → p1) → ((False ∨ (p3 → (False → p5))) ∧ (p3 ∧ ((p1 ∧ p2) ∨ (p3 → p5)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354870527194660964242063431914 : (p5 → ((False ∧ (((((((p3 → (p4 → p1)) → (p5 ∧ p2)) ∧ ((False ∧ p1) ∨ p2)) ∧ True) → False) ∨ (False ∧ (False → p4))) ∧ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803954785338614432585607463793 : (((p3 → (((((p4 ∧ (((p3 ∧ p2) ∧ ((p5 ∧ p3) → (False ∨ p5))) → p2)) ∧ p2) → (True ∧ p5)) → p4) ∧ ((p4 ∨ True) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244998247260336512237066181410 : ((p1 ∧ p4) ∨ ((((False ∨ p4) ∧ ((p5 ∨ p4) ∧ ((p3 ∨ (False ∧ (p1 → p3))) → p3))) ∨ p4) → (False ∨ ((p2 ∨ p4) ∨ (False ∧ True))))) := by
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
    cases h3
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h4.left
      let h8 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245426197704936159499259407076 : ((p2 ∧ p4) ∨ ((((p3 → p4) ∧ (p3 ∨ (p5 ∧ p5))) ∨ (p3 → (False ∧ True))) → ((p4 ∨ True) ∨ (((p5 ∧ (False ∧ p2)) ∧ p3) ∧ p4)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260814056873234038919592582014 : ((p3 → p5) → (p3 ∨ (p1 ∨ ((p4 → (((p5 ∧ (p5 ∧ (p4 ∧ (((p4 → True) → ((p4 → p1) ∧ p5)) → p1)))) → p3) ∧ p3)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135755497570681562921957505952 : (((p2 ∧ ((p3 → ((True ∨ p5) ∨ (p3 ∧ ((p2 → True) ∨ p3)))) → p1)) ∨ (True ∧ (p2 ∧ (True ∧ (p1 ∨ p3))))) ∨ ((p4 ∨ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64442876794592614849187287645 : ((p1 ∨ (((True → False) → ((False ∨ p2) ∨ (p2 ∧ (p5 → (p2 → (p2 ∨ (((p2 ∧ True) → (p2 ∧ p2)) ∨ p3))))))) ∨ (True → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780196424359816840671346190482 : (((p2 ∨ ((((((p3 ∧ ((p4 ∧ (p5 ∨ p4)) ∨ (p1 ∧ p4))) ∨ True) → (p2 ∧ False)) ∨ True) ∨ (True ∨ p1)) ∨ (p5 ∧ (p3 → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_552849433304181286379044640856 : (((p2 ∨ (((p3 ∨ (((p4 → (True ∨ (((False → (p2 → (p1 ∨ ((False ∧ p1) ∧ True)))) ∨ True) ∨ False))) → p1) ∧ True)) ∧ p4) ∨ True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_40933327771955520558305327000 : ((((((False → (((p4 → ((((p2 ∧ p2) ∨ (True → (p4 → p1))) ∨ p3) ∧ p5)) → True) ∨ p2)) ∧ False) ∨ False) ∨ (p2 ∧ False)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687082851651070903405672683633 : ((((False → ((True → p4) ∨ ((True → p3) ∧ ((p5 ∧ (((p2 ∨ p2) → p4) ∨ False)) ∨ p3)))) → (((True → False) ∨ (p5 ∨ p1)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340748092017568648245374322900 : (p2 → (((((((p1 ∨ p4) ∧ False) ∧ (True → p4)) ∨ p3) ∧ (p4 ∧ ((((p4 → p2) ∨ ((p5 ∧ True) → p1)) ∧ p5) ∨ p1))) ∨ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342657279410891657773705697172 : (p2 → ((((p5 ∨ p1) → (((p5 → False) ∨ p3) ∨ p1)) → p5) ∨ (((((p1 ∧ p1) ∧ (False → p5)) → (False ∨ (True → False))) ∧ p3) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137903873452123667071700171112 : ((p4 ∨ (((((p4 ∨ p1) ∨ (p2 ∧ ((False → p3) → True))) ∨ p4) ∨ p5) ∧ (((p3 → p3) ∧ p3) ∧ (p1 ∨ p2)))) ∨ ((True → p2) → p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58703676044330430807306988207 : (((p2 → p5) ∧ ((((((p2 ∨ p4) → (p1 ∧ (p2 ∨ False))) ∧ ((p2 ∧ p1) → (p4 ∧ p2))) ∧ (False ∨ (p5 ∧ False))) ∨ p1) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111864019035457163444680607413 : ((((True ∨ (p1 ∧ ((True ∨ (((((p2 → False) ∧ p4) → True) ∧ p1) → p1)) ∧ True))) ∧ (((p2 ∨ p5) ∧ False) ∧ p4)) ∨ p1) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113592230561467454098565164679 : (((p5 ∧ (((((p4 ∧ (True ∧ ((True ∧ p2) ∨ p3))) ∧ (p2 ∨ p4)) → p1) ∨ (p2 ∨ (False ∨ p4))) ∨ p1)) ∨ (p5 ∧ p2)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730126439466811907066390759020 : (((((p4 ∨ p2) → p3) → (((p4 ∨ ((p2 ∧ p2) → (False ∧ (((False ∨ p2) ∨ ((p2 ∨ p4) ∨ p5)) ∧ (p3 ∨ p4))))) → p1) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_661863330726567174720938123981 : (((((p4 ∧ ((p1 ∧ ((((True ∨ True) ∧ p3) → p1) → (p5 ∨ p4))) → (False ∧ p5))) → (p4 → ((p5 ∨ p5) → p4))) → (p4 ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60815588864941860286574981954 : ((True ∧ (p4 ∧ ((p4 ∨ ((((((True ∧ ((p3 ∧ p4) ∨ p4)) ∧ (False → p5)) ∨ p2) ∧ False) ∨ (p5 ∨ (p1 ∨ p1))) ∨ True)) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650717477498066172096393655458 : ((((((p3 → (False → p2)) → (p2 ∧ ((p3 ∨ p1) → p1))) → ((p5 → p1) → ((((True ∨ p2) ∧ p5) ∧ False) ∨ p1))) ∧ (p1 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68116402071338303343301802147 : ((p2 → (p3 → (((((p3 → p4) → p5) ∨ p4) ∧ (((p4 → p1) ∧ ((p3 ∧ (p1 ∧ (p1 ∨ p5))) ∧ p3)) ∨ (False ∧ p3))) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751585204858330204048297268196 : (((True ∧ (p1 ∧ (p2 ∨ ((False ∨ (p2 → p4)) → (p5 ∨ (p4 → ((p1 ∨ (True ∧ p5)) ∨ ((((True ∧ p3) ∧ p5) ∧ False) ∨ True)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228930230524625671906794672771 : ((p4 ∨ (p3 ∨ False)) ∨ (((p5 ∨ (p2 ∨ ((True ∨ (False → (p1 ∧ (True → (False → ((p2 ∧ (p2 ∧ False)) ∨ p5)))))) ∨ p5))) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594312341113965552236587652734 : ((((((p3 → (((((p1 → p1) ∧ ((p2 → p5) → True)) ∨ p4) → p5) ∨ p5)) → False) ∧ ((False → (p4 ∧ p1)) ∧ (p4 ∨ p3))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113443374905884966821129615843 : (((((p2 ∧ p5) ∨ ((p3 ∧ (p2 ∨ (((p2 ∨ p1) ∧ p1) ∨ ((False → p1) → (False → p1))))) ∧ p4)) ∨ True) ∨ (p5 ∨ p1)) ∨ (p1 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164734656039413239733774106582 : ((((((True ∨ (p1 ∨ (p3 ∧ (False → (False ∨ p3))))) ∧ p5) ∧ p1) ∧ (p4 → True)) ∨ p4) ∨ ((p4 ∨ p1) ∨ ((p1 → (True ∨ p1)) ∨ p1))) := by
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
theorem thm_5_vars_94885902678306995601327720110 : ((p3 ∧ (p5 ∧ (((p4 → p5) → False) ∧ (p5 ∧ ((((True → (p5 ∨ p2)) ∧ (((False ∧ p5) → False) → (p2 ∨ p4))) ∨ False) ∨ p1))))) → False) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h14 : (p4 → p5) := by
        -- Implications on the right can always be decomposed.
        intro h15
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h16 := h6 h14
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h19 : (p4 → p5) := by
      -- Implications on the right can always be decomposed.
      intro h20
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h21 := h6 h19
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330480501078461297159588069532 : (True → (p4 ∨ ((True ∧ (p4 ∧ ((((p4 → True) ∨ ((False → p5) ∧ ((p2 → p2) → p1))) → ((False ∧ p4) → p1)) → (p4 ∧ p2)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775173165071794786250532293890 : (((False ∨ ((p5 ∨ p1) ∨ (((p3 ∧ ((((p1 ∧ True) ∨ False) ∨ (((p2 → (False ∨ p1)) ∨ (p4 ∨ p4)) → p4)) ∨ p5)) ∨ p4) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345350605935761775772522161955 : (p3 → (((p5 → ((((((p4 ∧ ((True ∨ (True → p1)) ∨ p5)) ∨ p1) → p3) ∨ p1) ∨ ((p1 ∧ False) → p3)) → (True → False))) ∧ p4) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301005555608904093305553654908 : (False ∨ ((True ∨ (((p4 ∧ False) → ((False ∧ p2) ∧ p1)) ∧ (p5 ∨ p5))) → ((((p5 → ((p5 → p1) ∧ p5)) ∧ True) ∨ p1) ∨ (False → False)))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57711923472747464092943632652 : ((((p4 ∧ p2) → p4) → ((((True ∧ (p1 ∨ ((((False ∧ True) ∨ p5) → p2) ∨ p3))) ∨ (p5 → (p5 → (p1 → True)))) → p4) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157299177468933965755677843078 : ((((p1 → p5) → (((((p2 ∧ p5) → p1) → (p5 ∨ ((False ∧ p1) → p2))) ∧ p1) ∧ p2)) → False) ∨ ((p2 ∨ (p3 ∧ p1)) → (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140026515028403411029375812321 : (((((((((p1 ∧ True) ∨ ((p3 ∨ True) ∧ (p2 ∧ p2))) → p1) → p1) → p5) ∧ p2) ∧ (True ∨ True)) ∨ (p1 ∧ p2)) → ((p5 ∨ p2) ∨ p3)) := by
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
    cases h4
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657287568731406640606118214976 : (((((p1 ∧ p1) ∧ (p2 ∧ (True ∧ ((p5 ∨ (False ∨ ((True ∨ ((p2 → (p5 ∨ True)) ∨ p2)) ∧ (p5 ∨ p5)))) ∧ p4)))) ∨ (p2 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218058278083406717442097454696 : (((p3 ∨ p4) ∧ (False → True)) → (True → ((p1 ∧ (((p2 ∨ (((p5 ∧ False) ∧ p1) ∨ (((False ∧ True) ∨ p3) ∧ p4))) ∨ True) ∧ True)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49371976499473676192037006540 : (((p4 → (True → (((((False ∧ p4) → p4) → (p1 ∨ p3)) ∨ ((p4 ∨ p2) ∨ (False → p4))) ∨ (False ∨ p2)))) ∨ ((p4 ∧ p5) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42595458853329063519808923707 : (((p2 ∨ (p4 ∧ ((p4 ∨ (((p4 → ((((p5 → True) ∧ True) ∧ p2) ∨ ((p1 ∧ p3) → (p1 ∨ p2)))) → False) → p5)) ∧ True))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208353342679787475533689159296 : (((True ∧ True) ∨ ((p5 ∧ True) ∨ p3)) → (((((p4 → p5) → ((p5 ∨ p3) ∧ False)) ∧ ((p4 → False) → True)) ∧ p1) → (p5 → (p1 → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h12 : (p4 → p5) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h14 := h7 h12
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h20 : (p4 → p5) := by
        -- Implications on the right can always be decomposed.
        intro h21
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h22 := h7 h20
      -- We need to get the right conjuct of h22 based on <expert-advice>.
      let h23 := h22.right
      -- False on the left can always be used.
      apply False.elim h23
    case inr h24 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h25 : (p4 → p5) := by
        -- Implications on the right can always be decomposed.
        intro h26
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h27 := h7 h25
      -- We need to get the right conjuct of h27 based on <expert-advice>.
      let h28 := h27.right
      -- False on the left can always be used.
      apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259734509431269467036878271564 : ((p1 → p2) → (((((p1 ∨ p5) ∨ (p2 ∧ ((((p4 ∧ p1) ∨ True) → (p3 → ((p2 ∨ True) ∧ p4))) → (p3 ∨ p5)))) ∨ False) ∨ True) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180986359086722951798974447629 : (((p1 ∧ False) ∨ ((((False ∧ p5) ∧ (p4 ∨ p2)) ∧ p3) → (p1 → True))) → ((True → (False ∨ p2)) ∨ ((False → (p5 ∧ p1)) ∧ (p5 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h6
    -- False on the left can always be used.
    apply False.elim h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39049962887716155689135654924 : ((((p1 ∧ p2) ∨ ((True ∨ ((p5 ∨ (True ∧ (p5 ∧ p4))) ∧ (p2 → False))) → (True ∧ ((p1 ∨ p5) ∨ (p1 ∨ (p1 → p2)))))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310381458338109845209223860104 : (p2 ∨ (((((p2 → True) ∧ p2) ∨ (p2 ∧ p5)) ∧ False) ∨ (((True ∧ p2) ∨ (p3 ∨ False)) → (p5 → ((p5 ∨ p4) ∨ ((p2 ∧ False) ∧ False)))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41788010024756983263626749903 : (((((p1 ∧ (p1 ∧ False)) → p3) → ((((False ∧ p2) ∨ (p3 → ((p4 ∨ True) ∧ ((False → p5) ∨ p5)))) ∨ (p3 → True)) ∧ False)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302009591759558674501325647153 : (False ∨ (True ∧ ((((p3 → (p4 ∧ ((((p1 → p4) ∧ (p3 ∨ p2)) ∨ False) ∧ False))) ∧ ((p4 ∨ p5) ∧ (p3 ∨ (p5 → p3)))) ∧ p2) ∨ True))) := by
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
theorem thm_5_vars_60045441984155946789156018950 : (((p1 ∨ p5) → (True ∧ (((((p4 ∨ ((p2 → True) → p4)) ∧ ((p2 ∧ p4) → ((p2 → p3) ∧ (False ∨ False)))) ∨ p1) ∨ True) ∨ p3))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677819073326044933701966422952 : (((((((((p4 → p3) → False) ∧ (p2 ∨ (p2 ∧ (p5 ∨ p4)))) ∧ p4) ∨ (p2 ∧ p3)) ∧ (p3 ∧ p3)) ∨ (True ∨ ((p1 ∨ p5) ∧ p5))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_47672192074095654945586489272 : ((((((p2 ∨ p1) ∨ p4) ∧ (((p4 ∨ (False ∧ p5)) ∧ (((p5 ∨ (False ∨ (False ∧ p5))) ∧ True) ∧ p4)) → p1)) ∧ p5) → (p4 → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119152575734488496793705228200 : ((p2 → (((False ∧ (p2 → ((((p1 ∧ p5) → (p3 ∧ True)) → (p3 ∧ (p4 ∨ (False ∧ p5)))) → (p4 ∧ p5)))) ∨ p1) ∧ p1)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53766217214638571683867412376 : (((((((True ∨ p2) → (False → True)) ∧ p3) ∧ p5) ∨ p2) ∨ ((p1 ∧ p4) ∨ ((p3 ∧ ((((p4 ∧ p5) ∨ p5) → False) → p5)) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43254979269716892932901425492 : ((((p1 → (((((p5 → False) → ((((p2 → p3) → p5) ∧ ((p2 → False) → (p2 ∧ p3))) ∨ p3)) ∨ False) ∨ p4) ∨ p3)) ∧ True) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38206593222263184960406371318 : (((((((p5 → (p1 ∨ (False ∧ p1))) → (p4 ∨ p4)) ∨ ((False ∨ (True ∨ p4)) ∨ p4)) → (True → p1)) → (p2 ∨ (False ∨ p4))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638425265578681192064215760354 : (((((True → (((p3 ∨ True) ∨ p5) ∧ p1)) ∧ (p1 → ((((p1 → p1) → (p5 → False)) → p1) → ((False ∨ (p5 ∧ p5)) ∨ True)))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41533027224029476581645401495 : ((((((p5 → (((p5 ∨ p2) ∨ p2) ∧ p5)) ∧ p3) ∨ p2) ∨ (p4 ∧ ((p3 → ((False → (p4 ∨ (p3 → p3))) ∨ p1)) → False))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200762547033647706965797644974 : ((p4 ∧ (((p3 → (p4 ∨ True)) → False) ∨ True)) → (p1 ∨ ((((((p5 → (p1 → p3)) → p2) ∧ (p2 → (p1 → True))) ∨ p5) ∨ True) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56343513905620561752452442430 : (((((p1 ∧ p3) → p1) ∨ p4) → (p5 → (p4 → (p5 → (((p1 → ((p3 ∨ (True ∧ p1)) ∧ ((p1 → p5) → True))) → p2) ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46514063125754316012452905618 : ((((p2 ∨ p4) ∧ ((p1 ∨ (p3 ∧ (((p1 → p5) ∧ p2) ∧ ((p1 → ((p5 ∨ (p3 ∨ False)) ∨ p4)) ∨ False)))) ∧ False)) ∧ (p3 → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204657555715808181130784352599 : (((p4 ∧ ((p2 ∨ p5) ∨ True)) ∨ p3) ∨ (p4 → (((p4 → p2) ∧ ((((p5 → p5) ∧ ((False ∨ p2) ∧ (p4 ∨ p3))) → p1) → p4)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_5604787203924404682797343663 : ((((((p2 ∧ (p4 ∨ ((p5 ∨ ((((False → p4) ∨ False) ∨ ((p4 → False) ∧ True)) ∧ p4)) ∧ p3))) → p2) → False) ∨ (p3 ∨ True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_85442541218401971493079741316 : (((p5 ∧ ((False → p1) → (((p5 ∨ False) ∧ False) ∧ (p3 ∧ p1)))) ∧ (((p4 ∨ (((True ∨ p5) ∧ False) → p3)) ∧ (True → p3)) ∧ p1)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h11 : (False → p1) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- False on the left can always be used.
      apply False.elim h12
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h13 := h5 h11
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h17 : (False → p1) := by
      -- Implications on the right can always be decomposed.
      intro h18
      -- False on the left can always be used.
      apply False.elim h18
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h19 := h5 h17
    -- We need to get the left conjuct of h19 based on <expert-advice>.
    let h20 := h19.left
    -- We need to get the right conjuct of h20 based on <expert-advice>.
    let h21 := h20.right
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329565833020083650142902781139 : (True → ((p2 ∨ p3) ∨ ((p1 ∨ p3) ∨ ((((p2 ∧ (((True → (p5 ∨ p2)) ∧ (p5 ∨ True)) → p4)) ∨ (p3 ∨ True)) ∧ p5) ∨ (False → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308590335034037341173336881314 : (p2 ∨ ((((p3 ∨ p5) ∨ p1) ∨ ((p4 → ((((p4 ∨ (False → p5)) ∧ (True ∨ (p1 ∧ p5))) ∧ p5) ∨ ((False ∧ p4) → p2))) ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661206153910718809452357482499 : ((((((p5 → (p2 ∧ (p1 → True))) ∧ (p3 → ((p1 ∧ p1) → ((p1 → p2) ∧ (p2 ∧ (p5 → p5)))))) ∨ (False ∨ p3)) → (p3 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950159104704427156219277065462 : (((((p3 ∨ p5) → False) ∧ ((((False ∨ (((p5 → (p3 ∨ False)) → (p5 → p5)) ∨ p1)) ∧ True) ∧ p5) ∧ (((p5 ∧ p5) ∨ True) ∨ p1))) → False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h17 : (p3 ∨ p5) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h16
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h18 := h2 h17
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h20 : (p3 ∨ p5) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h7
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h21 := h2 h20
          -- False on the left can always be used.
          apply False.elim h21
      case inr h22 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h23 : (p3 ∨ p5) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h24 := h2 h23
        -- False on the left can always be used.
        apply False.elim h24
    case inr h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h26 =>
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- Conjunctions on the left can always be decomposed.
          let h28 := h27.left
          let h29 := h27.right
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h30 : (p3 ∨ p5) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h29
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h31 := h2 h30
          -- False on the left can always be used.
          apply False.elim h31
        case inr h32 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h33 : (p3 ∨ p5) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h7
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h34 := h2 h33
          -- False on the left can always be used.
          apply False.elim h34
      case inr h35 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h36 : (p3 ∨ p5) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h37 := h2 h36
        -- False on the left can always be used.
        apply False.elim h37
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354809730281971228393645501307 : (p5 → (((((False ∨ p5) ∧ p2) → False) → ((p1 ∧ (((((True → ((p2 ∨ p2) → False)) ∧ p3) → p4) → True) ∨ (p2 ∨ p4))) → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262146542440955799919599351219 : (True ∧ ((((p1 ∨ ((((False ∨ ((p1 ∨ ((p4 → p1) ∧ p3)) ∧ p5)) ∨ p5) → (True ∨ (p3 → p5))) ∨ (True ∧ p5))) → p1) ∨ p5) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94799960086068157372693462894 : ((p3 ∧ (((p2 → p2) → False) ∧ ((p2 ∨ ((((p3 → (((p4 ∧ p2) → ((True ∧ p5) ∧ p2)) → p2)) ∧ p5) ∨ True) ∨ p1)) → p2))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p2 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117071049292499696555145431754 : (((True → p2) → (((p1 ∨ (((p1 → p5) ∨ (p5 ∨ ((p3 ∨ (p4 ∧ (False ∨ p4))) ∧ p2))) ∨ (p1 ∧ p5))) ∧ False) ∨ True)) ∨ (False ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180442219973158460112623554521 : ((((False ∨ ((False ∧ p3) → p5)) ∨ (p4 ∨ (p1 → p2))) → (True → p3)) → (((p3 → (p3 ∨ False)) ∧ p3) ∧ ((False ∨ p3) ∧ (p4 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∨ ((False ∧ p3) → p5)) ∨ (p4 ∨ (p1 → p2))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h3
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- One of the premise coincides with the conclusion.
  exact h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : ((False ∨ ((False ∧ p3) → p5)) ∨ (p4 ∨ (p1 → p2))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h14 := h1 h10
  -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
  have h15 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h14, we can now drive its conclusion.
  let h16 := h14 h15
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h16
  -- Implications on the right can always be decomposed.
  intro h17
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h18 : ((False ∨ ((False ∧ p3) → p5)) ∨ (p4 ∨ (p1 → p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h17
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h19 := h1 h18
  -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
  have h20 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h19, we can now drive its conclusion.
  let h21 := h19 h20
  -- One of the premise coincides with the conclusion.
  exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160809515729689106180981466757 : (((p2 → (False → (True ∨ (False ∨ p3)))) ∨ (((p4 → p2) ∧ (False → p4)) ∨ (p3 ∧ (p2 ∨ p3)))) → ((p3 → p2) ∨ ((False ∧ p4) → True))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178881448612100926211223134563 : (((p3 ∧ False) ∧ (((p2 ∨ (p4 ∨ p4)) ∨ (p2 ∧ (p4 → p2))) ∧ False)) ∨ ((False → ((p5 → p1) ∨ p5)) → (p5 ∨ ((True ∧ True) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_301794046721023355253735803118 : (False ∨ ((p3 ∧ p3) ∨ (p3 → (p3 → ((False ∨ p5) ∨ ((p5 → (((p4 ∧ (p5 ∨ ((p5 → p5) ∧ True))) ∧ False) → p2)) ∧ (False → p1))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h13
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41636174572651419897416395601 : ((((p3 ∨ (False → (p1 ∨ (p4 ∧ (p1 ∧ False))))) → ((((p3 → (p1 → (True ∧ p1))) → p2) ∨ (p4 ∨ (True ∧ p2))) ∨ True)) ∨ False) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_133627536066323723365740996417 : (((((True ∨ False) → ((True ∨ p2) ∧ ((((p4 → ((True ∨ p3) ∧ p2)) ∨ p4) ∨ False) → (p2 ∧ p5)))) → p4) ∧ False) ∨ (True → (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179456134289312348282579594756 : ((p5 ∨ ((p1 ∨ p1) ∧ (p3 → ((p1 ∨ (p2 ∧ p4)) ∨ (p3 ∧ p1))))) ∨ (p2 → ((False → p1) ∧ ((True ∨ (p4 ∧ (True ∨ p2))) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657737735847502339587712616665 : ((((True ∧ (((False ∨ (((p4 ∧ p1) → ((p2 ∧ (True → (p4 → p2))) ∨ p2)) ∧ (p4 ∧ p3))) ∨ (p5 ∧ p5)) ∨ True)) ∨ (False ∧ True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168661340057781638313286443718 : ((p4 ∧ (p2 → ((((p4 → p3) ∧ (True ∨ p1)) ∧ (False ∧ ((False ∨ p3) ∧ p1))) ∧ p5))) → (p4 → ((p3 ∨ ((p2 ∨ p4) → p2)) ∨ True))) := by
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
theorem thm_5_vars_962417824362629563909385377329 : ((((True → False) ∧ ((p3 ∨ p5) ∨ ((((((p4 ∨ p4) ∨ (p5 ∧ (True ∨ p3))) ∧ p1) ∧ (p2 ∨ (p5 ∨ p5))) → (p4 → p5)) → p4))) → p1) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h9
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h12
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179448524569064689464393238892 : ((p5 ∨ (((((p5 ∨ True) ∨ p4) ∧ (p3 → p2)) → p5) ∨ (p3 ∧ p5))) ∨ ((p5 ∨ (p5 → (p5 ∨ p2))) → ((False → p2) ∨ (p5 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166181002444922129642386072106 : ((p1 ∧ ((p3 ∧ ((((False ∧ p1) → (p4 ∨ p2)) ∧ False) ∧ (p4 ∧ (False ∨ False)))) ∧ p5)) ∨ ((((p3 ∨ (p2 ∨ p3)) ∧ p2) → p2) ∨ p1)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133772449405390244802423255696 : ((((((p4 ∧ p2) ∧ p1) ∧ True) ∨ ((False ∨ (((p1 → p3) → p1) ∧ ((False ∧ False) → (p2 ∧ True)))) ∧ False)) ∧ p3) ∨ ((p4 ∨ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636011410038366544784476261499 : (((((((p1 ∨ (p4 → (p5 ∨ p5))) ∧ p2) → ((((p5 ∧ p3) → p3) ∨ p1) ∧ False)) ∧ (p4 ∨ (((p1 → p4) ∨ p3) ∧ True))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147026581686391733754454930720 : ((((p5 → (((p4 ∨ ((True → (p5 ∨ p5)) → p5)) ∨ (p5 ∨ p2)) ∧ p2)) ∧ (p4 ∧ (False ∧ p1))) ∧ p4) ∨ (((p5 ∧ False) → True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147358276102835783393411988723 : ((((p3 ∨ ((p4 ∧ (((p2 ∧ p2) ∨ (p2 ∧ p5)) → p3)) → (True ∧ p2))) ∨ ((p4 ∨ True) ∨ True)) ∨ p2) ∨ ((p4 → p4) → (False ∧ p3))) := by
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
theorem thm_5_vars_205601205407936655804443827416 : (((p5 → False) ∧ (p5 ∧ (p2 ∧ p2))) ∨ (p1 ∨ ((((p1 ∨ (False → p2)) ∧ (p2 ∧ True)) → ((True ∧ (False → (p4 ∨ p4))) ∧ p2)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h4.left
    let h10 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_17963785343285794572975400629 : (((((((p4 → (p3 ∨ p5)) ∨ p1) ∧ p4) ∨ (p5 ∧ p3)) → ((True ∨ ((p5 ∧ p4) ∧ p1)) → p3)) ∨ ((p2 ∧ False) ∨ (p5 → True))) ∧ True) := by
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
theorem thm_5_vars_207392107322838499648447933183 : (((p2 ∧ ((True ∨ p1) ∨ p4)) ∨ p3) → (((p3 ∧ (False ∧ ((p5 ∧ False) ∨ (p3 ∨ (p3 ∧ p5))))) ∨ (p2 → p3)) ∨ (False → (False → p5)))) := by
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
        -- Implications on the right can always be decomposed.
        intro h8
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Implications on the right can always be decomposed.
    intro h17
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684118371468729137215230812647 : ((((((p5 ∧ False) ∨ ((p5 ∧ ((False ∨ (False ∧ p2)) ∨ True)) ∧ (p1 ∨ False))) ∧ (p4 ∨ p5)) ∨ (p5 ∧ (((p4 ∨ p3) → True) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66647942341477995019238780098 : ((True → (((False ∨ ((p5 → ((p1 ∨ p1) → p4)) ∨ p3)) → p3) ∨ (((False ∧ p1) ∨ p3) ∨ ((True ∧ ((p3 ∧ p4) ∧ p1)) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791311283230672633199666557431 : (((True → (((((((p1 → ((p4 ∨ False) ∨ p4)) ∨ p2) ∨ ((p2 ∨ False) → ((p1 ∧ (p4 ∧ False)) ∨ p2))) ∨ p2) ∧ p5) → p2) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747252241307600651749588777532 : ((((p5 ∨ p2) → (((((p5 → (True → (p4 → False))) ∨ True) → p3) ∨ (p5 ∨ (p4 ∨ (False → (p3 ∧ p3))))) ∨ (p2 → (p5 ∨ p2)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310150399930156393088998839335 : (p2 ∨ (((True ∨ ((True ∨ p2) ∧ (p5 ∧ ((True ∧ p4) → p2)))) ∨ (True → p1)) → ((p4 ∧ p5) ∨ (((True → True) ∨ p2) ∨ (p1 → p5))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h7.left
        let h10 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h7.left
        let h14 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h16
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345669734896997892053529187888 : (p3 → ((p1 ∨ ((p4 → (p5 → (p2 ∧ (True ∧ (((p1 ∧ (p2 ∧ (p5 → p1))) ∧ False) ∧ ((False ∧ (p4 ∧ False)) → True)))))) ∧ p4)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53151751801938748443386476771 : (((((p2 → (((p5 ∧ (p2 ∧ p5)) ∧ True) → False)) → p3) ∨ p4) ∨ (False ∧ (p3 ∨ (p5 ∨ (p3 ∨ (p2 ∨ (p3 ∨ (p3 ∧ p1)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147552487801623531573716503966 : (((p5 → (((True ∧ p4) ∧ (False ∧ ((False ∧ False) ∨ (False ∧ p3)))) ∨ (((p4 ∧ p2) → p5) ∨ p2))) ∨ p4) ∨ ((False ∧ p5) → (True → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



