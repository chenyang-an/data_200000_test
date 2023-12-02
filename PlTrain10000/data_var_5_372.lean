variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172368527726822504769141218764 : (((p1 ∧ (((p3 ∧ p5) ∨ p2) ∧ p2)) ∨ (p4 ∧ ((False ∨ (p2 → False)) ∨ p2))) ∨ ((p1 → (True ∨ ((False ∧ (p2 ∧ p4)) → p1))) ∨ p1)) := by
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
theorem thm_5_vars_619519414991285032434665374206 : (((((p3 → (p4 ∧ p5)) → ((((p3 ∧ ((False ∧ (p4 ∨ ((p1 ∨ p5) ∨ p2))) ∧ (p2 ∨ p1))) ∨ p5) → p2) ∧ (False ∧ p4))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_51089754084939281521484609526 : (((((((((p5 ∧ True) ∨ True) ∨ p3) ∧ (p5 ∧ (p1 → (False ∧ p4)))) ∨ p2) → p3) ∧ False) ∨ (p1 → (p3 → ((p2 ∧ p3) ∨ True)))) ∨ p3) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50370473042896623436320572790 : (((((p4 ∨ True) ∧ p4) → ((p4 ∧ (p1 → p4)) → ((p1 ∨ ((p1 → True) ∧ (p2 → p5))) ∧ True))) ∨ (p4 → (p1 ∨ (p4 → p4)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164967230698190457113957092020 : ((((False ∨ ((((p3 → ((p1 ∧ True) → p1)) ∨ p4) ∨ p3) ∨ True)) ∧ (False ∨ p5)) → p2) ∨ ((p5 ∨ (((p1 → p5) ∧ False) ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328418265782662630241581109953 : (True → ((((p1 ∨ (p2 ∧ False)) ∨ ((p1 ∨ p1) ∨ p5)) → (p4 ∨ ((False ∨ (p1 → False)) ∨ True))) ∨ (((True ∨ True) ∧ (p2 ∨ True)) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700203794001642742998252475220 : (((((p2 → p1) ∨ ((True → (p2 ∨ p3)) ∨ ((False ∧ True) ∨ False))) → ((False ∨ (True ∧ p5)) ∧ ((p3 → (False → p2)) ∨ (p3 ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137305486914014438403054885748 : ((p2 ∧ ((((p1 ∨ ((True ∧ (True → True)) ∧ (True ∨ True))) ∨ ((p5 ∧ p3) ∧ p3)) ∨ False) → ((False ∧ p2) ∧ False))) ∨ (False → (p2 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197751227219423862518712467541 : (((p1 ∧ (False ∧ p3)) ∧ ((p1 ∨ p5) ∧ p1)) ∨ (p2 → (((True ∨ (((p3 ∨ p5) → True) ∧ p3)) ∧ False) ∨ (p1 ∨ (True → (p5 → True)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686500020149112353500190559041 : (((((p5 → (p1 → True)) ∨ ((p5 → (False ∧ p5)) ∨ (p1 → ((p5 ∨ p4) ∨ (True → p4))))) → ((False ∧ (p4 ∨ p5)) ∨ (True ∨ p3))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53664003685258228612520395666 : ((((p4 ∧ p1) ∨ (p1 ∧ ((p3 ∨ (p4 ∧ p1)) ∧ True))) ∧ (((p3 ∧ (((True ∧ p1) ∧ p4) ∨ ((p5 → p5) ∨ p5))) ∧ p2) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44878399146781091596408259738 : (((((p4 → p4) ∧ p5) → (((False → (p1 ∨ (p5 ∧ (p3 ∧ (p5 ∧ (True ∧ ((p1 → True) ∨ (True ∧ p4)))))))) ∨ p5) ∨ p2)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118145711114864978487226310206 : ((False ∨ ((((p2 ∧ p3) ∧ (((p1 ∨ p5) → p1) ∨ p2)) ∧ False) ∧ (((False → (p2 → (p4 → p4))) ∧ (True → False)) ∧ p5))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135741553396844225525576309235 : ((((((((False → p1) ∨ p1) ∨ p4) → p3) ∨ p3) → ((p2 ∧ True) → False)) ∨ ((False → p5) ∨ ((p2 ∨ False) → p4))) ∨ ((p1 ∨ p1) ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618352299592669178463899948164 : (((((False ∨ ((p4 ∧ p1) ∨ p3)) ∨ (((p3 ∨ p1) ∨ (True ∨ ((((p2 ∨ ((p2 → p1) ∧ p1)) → p4) ∧ p3) ∧ False))) ∨ p2)) ∨ p2) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157354395630667075028006031118 : (((True → (True → ((p4 ∨ ((False ∨ (((p3 ∧ (p2 ∨ p4)) → p1) ∧ p3)) ∨ p3)) ∨ True))) → p2) ∨ (p2 → ((p4 → (p2 → p3)) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305036860356550074652713335899 : (p1 ∨ ((p1 → ((False ∨ (((p5 ∨ (p3 ∧ True)) ∧ (True ∧ p5)) ∨ p4)) ∨ (((True → p2) → p5) ∧ (p1 → p4)))) ∨ (True ∨ (True ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618169730320938981240879528166 : (((((p1 → (p2 ∨ (False ∨ p4))) ∧ ((p2 ∨ (p4 ∨ (((p3 → (True ∨ p5)) ∧ p1) → ((p1 ∨ p4) ∨ p3)))) → (p3 ∧ p4))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48477559548039218276861199816 : ((((((p3 ∧ p4) ∧ (False → p2)) ∨ (False ∧ ((p2 ∨ (p5 ∧ (p3 ∨ (p2 → False)))) → (p5 → p4)))) ∧ p3) ∧ (p2 ∨ (p3 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314227230604280584122217002898 : (p3 ∨ ((((((p5 → ((p3 ∨ p1) ∨ p5)) ∧ (((p5 → p3) ∧ ((p2 → p3) ∧ p2)) → p5)) → p4) ∧ p3) ∨ True) ∨ (p2 ∧ (p2 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719453392034393344520059235312 : ((((p1 ∨ (True ∧ (p1 ∧ p5))) ∨ ((((p1 ∧ ((p4 ∨ (p2 ∨ p1)) ∧ (p1 → (p5 → (p1 ∨ (p5 ∨ p1)))))) ∧ True) ∧ p2) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_171926984991432179208962179190 : ((((p1 ∧ ((((p1 → p2) → p5) → (p1 → False)) ∨ p2)) ∧ p3) ∧ (p4 → p3)) ∨ ((p4 ∨ (((p3 → p4) ∧ True) ∨ (p2 → p4))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800211536841337054040051521825 : (((p2 → (((p3 → ((p2 ∨ (((p4 ∧ p1) ∨ (((((False ∨ True) → p4) ∧ (p1 ∨ True)) ∧ p2) ∧ p2)) → True)) → p2)) ∧ False) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258420438104408979733416400755 : ((p5 ∨ p1) → (((p1 → (True ∧ (p3 ∨ ((((p2 ∧ p3) ∨ p3) ∧ p3) → p5)))) ∧ False) ∨ (((False ∧ (p2 ∧ p1)) → (False → p4)) ∨ p2))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625901717765086528805857867959 : ((((p2 → (((p2 ∨ ((False ∨ (((((True ∨ True) → p2) ∨ False) → (p2 ∧ (p5 ∨ p3))) → False)) → (True ∨ True))) → p1) → p4)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111494480190971538552093984201 : (((p3 → ((p5 ∨ ((True ∧ ((p4 ∧ p1) ∨ (p4 ∨ True))) ∧ (p2 → p3))) ∨ ((p1 ∨ ((p4 ∧ True) ∨ p3)) ∨ True))) ∧ p5) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183983757771247323344866048237 : (((((((p5 ∨ p2) ∨ p4) ∧ (p2 ∧ p4)) → False) ∧ p4) ∨ False) ∨ (((((False ∨ p5) → p3) → (p4 ∨ p1)) ∨ (True ∨ p4)) ∨ (p3 ∧ p4))) := by
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
theorem thm_5_vars_165910311988464985589551399174 : (((p2 → (p5 → p5)) → (p5 ∧ ((True ∨ p1) → (True → ((p2 ∧ p5) → (False → False)))))) ∨ (True ∧ ((p5 ∨ True) ∧ (False ∨ (p4 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165535002710455934729642743726 : (((p4 → (p3 → (((p4 → False) ∨ (p5 → p4)) → p5))) → ((True → (True → p1)) → p1)) ∨ ((True → (p3 → p2)) → (p3 → (False ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179148835043818254191234502306 : ((p2 ∧ (((((False → p3) ∧ ((True → p3) → p4)) ∨ False) ∧ False) ∨ False)) ∨ (((p1 ∧ p3) → False) ∨ ((False ∧ ((p3 ∧ False) → p2)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111982785650274248294886633521 : (((((False ∨ (p4 → (p2 → True))) → True) → (False ∧ (p3 → (False ∨ (((True ∨ p3) ∧ ((p2 ∨ p5) → p5)) ∧ p5))))) ∨ p1) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608311373098740969178501897147 : ((((((((True ∧ (p1 ∨ ((p3 ∨ p2) ∧ False))) ∨ (False ∨ p2)) ∨ ((False ∨ ((True ∨ p4) ∧ (True ∨ True))) → p4)) ∨ p4) ∨ True) ∨ p3) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_171654809669002299508126980981 : (((False ∧ (p1 ∨ ((p4 ∨ ((((True ∧ p4) → p3) ∧ p4) ∨ p1)) ∧ True))) ∨ True) ∨ ((p4 → True) ∨ (((p5 → p5) → p5) ∧ (True → True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51114489007621808437932460443 : (((((p1 → (p4 ∨ (((p1 → p1) ∨ (False ∧ False)) ∧ (p2 → (p1 ∧ False))))) ∨ p2) ∨ False) ∨ (p5 → (p1 ∨ ((True ∧ False) → p2)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121284386528884749913971268457 : (((((((p4 ∧ (False ∨ (True ∨ (p1 → (p2 ∧ ((p3 → p5) → (p1 ∨ (p2 → False)))))))) ∨ p1) ∨ True) ∨ p3) ∧ True) → False) → (p1 ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p4 ∧ (False ∨ (True ∨ (p1 → (p2 ∧ ((p3 → p5) → (p1 ∨ (p2 → False)))))))) ∨ p1) ∨ True) ∨ p3) ∧ True) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340925165014532813096841108363 : (p2 → ((((p5 ∨ p5) ∧ (p1 ∧ (p3 → True))) ∨ ((((((p3 ∧ p1) → p4) ∧ (False → ((False → False) → p4))) → p5) ∨ p1) ∧ True)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46006342071259791478024891172 : (((((False ∧ ((p1 ∨ ((True ∧ ((True → p4) ∨ p4)) ∧ (False → p5))) ∨ p1)) ∨ (((p2 ∨ p4) → p5) ∧ p2)) ∧ p3) ∧ (False → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156948269575880264618204779395 : (((((p4 ∧ p5) ∧ (((((p4 ∨ p4) ∨ (p2 → False)) → p2) ∧ p2) → True)) → (p4 ∧ p3)) ∨ p5) ∨ ((False → p5) ∨ ((p5 → p5) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714421768754911880760187332984 : (((((p1 ∧ (False ∨ p4)) → (p5 ∧ p4)) → ((p3 ∧ ((p3 ∨ p3) ∧ (((((p5 ∧ p1) ∧ p2) ∨ (True ∨ p3)) ∧ True) → p4))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263141847139197791906378722703 : (True ∧ (((True ∨ p3) ∧ (((((p1 ∨ (p3 ∨ (p5 → (True ∨ p4)))) ∧ True) ∨ p2) → False) ∨ (p4 ∨ (p5 ∨ (p2 ∨ True))))) ∨ (p5 ∧ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_179475504850597679048158877327 : ((True → (((p4 → p3) ∨ (p3 ∨ ((False ∨ p1) ∧ (True → True)))) → p5)) ∨ (p2 ∨ ((p2 ∨ (False → (p1 ∧ (False ∧ p5)))) → (False → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244496211478206800525431481609 : ((False ∧ p3) ∨ ((p3 → (False ∨ (((p2 ∨ (p5 ∨ (((True ∧ p5) ∨ p3) → (p5 → ((p2 ∨ p5) → True))))) ∨ p3) ∨ (p3 ∨ p1)))) ∨ p5)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738898337574767672096657920267 : ((((p3 ∧ False) ∨ ((((True ∧ p5) ∨ (p1 → True)) → ((False → p3) → ((p2 → (False ∧ (p2 ∧ p2))) ∧ (p5 ∨ (True → p5))))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753301538583792485339267722612 : (((False ∧ (((p2 → (p2 ∧ ((True ∨ (p4 ∨ (True ∨ (False → p2)))) → ((((p5 ∨ True) → p4) → p5) ∧ True)))) → p3) → (p3 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355309102212693329787811983918 : (p5 → ((p2 ∧ ((((p3 ∧ (True ∧ False)) ∧ (p3 → ((False ∧ p3) ∨ p4))) ∨ (False ∨ (p5 → True))) → ((p3 ∧ p3) ∧ (p1 ∧ p3)))) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (((p3 ∧ (True ∧ False)) ∧ (p3 → ((False ∧ p3) ∨ p4))) ∨ (False ∨ (p5 → True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137423386753644804089430780333 : ((p4 ∧ ((True → (((p3 ∨ (((p5 ∨ ((p3 ∨ p3) ∧ p3)) → p4) ∨ p4)) ∧ ((False ∧ p5) ∨ p1)) ∨ p4)) ∨ p5)) ∨ ((p4 ∧ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662525917204239102724566456761 : (((((((False ∨ True) → False) → (p3 → p4)) ∨ (((True → p5) ∨ (((p2 ∨ (False ∧ p5)) ∨ p3) ∨ (p1 ∧ p4))) ∨ p2)) → (False ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660330553517688602252576312440 : (((((True ∨ ((p1 → (True → (p5 ∧ True))) ∧ ((p4 → (p2 ∨ p4)) → (((p5 ∨ p5) → False) → (p1 → True))))) ∨ p5) → (p2 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193770093505136051281824739200 : ((p3 ∧ (p4 → ((True ∨ p5) ∧ (p3 → (True ∧ True))))) → (((True → False) ∧ True) → (((p5 ∧ (p4 → False)) ∨ ((True ∧ p2) → p5)) → p4))) := by
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
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h2.left
    let h8 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h12 := h7 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h2.left
    let h15 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h1.left
    let h17 := h1.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h18 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h19 := h14 h18
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261215495223421338205859755191 : ((p4 → p5) → (((((p4 ∨ True) ∨ p5) ∨ (p5 → p2)) → ((p1 ∧ p4) ∧ p2)) ∨ (((True ∨ p3) ∨ p1) ∨ ((False → (True ∧ False)) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_301846048839043301124095852950 : (False ∨ ((p5 ∨ p5) ∨ ((p3 ∨ p3) → (p2 ∨ ((((p4 ∧ ((p1 ∨ p1) ∧ (p4 ∨ False))) ∨ (p3 → (p2 ∨ (p3 → p1)))) → True) → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41741785065120828653401367519 : ((((p5 ∨ ((p5 ∨ True) → False)) ∧ (((p5 → (((p5 ∧ p5) → (p3 ∧ p3)) → (True ∨ p5))) ∨ (p5 ∨ False)) → (False ∨ p3))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52326804672403307054877612842 : ((((p5 ∧ (((False ∨ ((p3 → False) → (False → p1))) ∨ p2) → p1)) ∨ p3) ∧ (True ∧ (((p5 → p3) ∨ False) ∧ (p4 ∨ (False ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135061881152625754256089861078 : (((((p3 ∧ (p4 ∧ False)) ∨ (p4 → ((False ∨ p1) → (((p5 → (p4 ∧ p5)) → p2) ∨ p1)))) → p1) ∨ (p2 ∧ False)) ∨ ((p5 ∧ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115318955097009564402653103495 : (((((True ∨ p5) ∨ p3) ∨ ((p4 ∧ p1) ∧ (p1 ∧ p5))) → (((True → p4) ∨ (p4 ∧ p5)) → (False ∨ ((p3 ∧ p2) → p4)))) ∨ (p2 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
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
          -- Conjunctions on the left can always be decomposed.
          let h8 := h7.left
          let h9 := h7.right
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h10 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h11 := h3 h10
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h13
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h16 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h17 := h3 h16
          -- One of the premise coincides with the conclusion.
          exact h17
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h22 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h23 := h3 h22
        -- One of the premise coincides with the conclusion.
        exact h23
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h25.left
      let h28 := h25.right
      -- Conjunctions on the left can always be decomposed.
      let h29 := h26.left
      let h30 := h26.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h31
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- One of the premise coincides with the conclusion.
      exact h27
  case inr h34 =>
    -- Conjunctions on the left can always be decomposed.
    let h35 := h34.left
    let h36 := h34.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h37 =>
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h38 =>
        -- Disjunctions on the left can always be decomposed.
        cases h38
        case inl h39 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h40
          -- Conjunctions on the left can always be decomposed.
          let h41 := h40.left
          let h42 := h40.right
          -- One of the premise coincides with the conclusion.
          exact h35
        case inr h43 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h44
          -- Conjunctions on the left can always be decomposed.
          let h45 := h44.left
          let h46 := h44.right
          -- One of the premise coincides with the conclusion.
          exact h35
      case inr h47 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h48
        -- Conjunctions on the left can always be decomposed.
        let h49 := h48.left
        let h50 := h48.right
        -- One of the premise coincides with the conclusion.
        exact h35
    case inr h51 =>
      -- Conjunctions on the left can always be decomposed.
      let h52 := h51.left
      let h53 := h51.right
      -- Conjunctions on the left can always be decomposed.
      let h54 := h52.left
      let h55 := h52.right
      -- Conjunctions on the left can always be decomposed.
      let h56 := h53.left
      let h57 := h53.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h58
      -- Conjunctions on the left can always be decomposed.
      let h59 := h58.left
      let h60 := h58.right
      -- One of the premise coincides with the conclusion.
      exact h54



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116712761337450405132794402285 : (((p1 ∧ p5) ∨ (((p4 ∧ p5) ∧ (False ∧ (p3 ∧ False))) ∨ (((((p4 ∧ (p5 ∧ (p2 → True))) → False) ∨ p3) ∧ True) ∧ p5))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322500017762605272346059293004 : (p5 ∨ (((True → p3) → (((p1 → True) ∧ ((p5 → p4) ∨ (p5 ∧ (p4 ∨ (p3 ∨ ((p3 → True) ∧ ((p3 → False) ∧ p3))))))) → p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184452708544670628918204807091 : (((p1 ∨ ((True → p2) → (False ∧ (p1 ∨ p5)))) ∧ (p1 → p4)) ∨ (True ∨ ((p5 → (((True ∧ (p2 → (p1 → True))) → False) ∧ p2)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47725047881791399736158681720 : (((((p3 → ((((((p3 → ((True ∨ p2) ∨ False)) ∨ p1) → False) → ((False → p1) ∨ p3)) ∧ False) ∨ p2)) → p5) ∨ p3) → (p4 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139179738333158975698171009665 : ((((False ∨ ((False ∨ p5) ∧ (p5 ∨ p1))) ∧ (((False ∨ p4) → True) ∨ (((p2 ∧ True) ∧ p3) ∨ (p4 ∧ p4)))) ∨ False) → ((p2 ∧ p4) ∨ True)) := by
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
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h4
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h13 =>
            -- Disjunctions on the left can always be decomposed.
            cases h13
            case inl h14 =>
              -- Conjunctions on the left can always be decomposed.
              let h15 := h14.left
              let h16 := h14.right
              -- Conjunctions on the left can always be decomposed.
              let h17 := h15.left
              let h18 := h15.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h19 =>
              -- Conjunctions on the left can always be decomposed.
              let h20 := h19.left
              let h21 := h19.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
        case inr h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h4
          case inl h23 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h24 =>
            -- Disjunctions on the left can always be decomposed.
            cases h24
            case inl h25 =>
              -- Conjunctions on the left can always be decomposed.
              let h26 := h25.left
              let h27 := h25.right
              -- Conjunctions on the left can always be decomposed.
              let h28 := h26.left
              let h29 := h26.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h30 =>
              -- Conjunctions on the left can always be decomposed.
              let h31 := h30.left
              let h32 := h30.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
  case inr h33 =>
    -- False on the left can always be used.
    apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135881227605687296113380348174 : (((p2 ∧ (((p3 ∧ p2) → p1) ∧ ((False ∨ (p3 → p3)) → p3))) ∨ ((((p3 ∨ p5) → (True ∧ p3)) ∧ p5) ∧ p2)) ∨ ((p2 ∨ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735311686656406591982570620993 : ((((p4 ∨ False) ∧ (((((p5 ∧ p5) → (p1 ∨ p4)) → ((((True ∧ p4) ∧ False) ∧ p5) ∧ ((True → True) → True))) ∧ (p1 ∧ p3)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_918063228283773392821468300910 : ((((True ∧ (((True ∧ p3) → p2) ∨ (((p4 → (p3 → p2)) ∨ p3) ∨ (True ∨ p2)))) → ((p5 ∨ p5) ∧ ((True ∧ p3) ∧ (False ∨ False)))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∧ (((True ∧ p3) → p2) ∨ (((p4 → (p3 → p2)) ∨ p3) ∨ (True ∨ p2)))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47934246703867497419752021492 : ((((p4 ∨ (((p1 ∧ (True ∧ p1)) ∧ p2) → (((p4 ∧ p2) ∨ p3) ∨ (p1 ∧ (False ∧ True))))) ∧ (False ∨ (p2 ∨ True))) → (p4 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_17237368981522840566117565332 : (((((p5 ∨ (((p2 ∧ p1) ∨ (p5 ∧ True)) ∨ p4)) ∨ p3) ∧ (p2 ∧ ((((True → True) ∧ True) ∧ p3) → p4))) → ((p5 ∧ p1) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h3.left
      let h7 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Conjunctions on the left can always be decomposed.
          let h13 := h3.left
          let h14 := h3.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- Conjunctions on the left can always be decomposed.
          let h18 := h3.left
          let h19 := h3.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h3.left
        let h22 := h3.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h3.left
    let h25 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133906377388640334670795065218 : (((p2 ∨ ((((p4 ∨ (p5 ∨ p1)) ∧ p5) ∧ (((True → True) → p4) ∨ ((True ∧ p3) → p2))) ∨ (p1 ∧ True))) ∧ p3) ∨ ((p1 → True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620007482176053123206064636059 : (((((p3 → False) ∧ ((p1 → ((True ∨ p3) ∧ (p5 ∧ ((p3 ∧ p3) ∧ (False → p5))))) → ((((True ∨ False) ∨ p2) → p1) ∧ p3))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206144746806212376039859542429 : ((p4 ∧ (p2 → ((p3 ∨ False) → p4))) ∨ (((((p1 → False) → False) ∧ p1) ∨ True) ∨ (((p3 ∧ p5) ∧ p3) ∨ ((p1 ∧ p1) ∧ (p4 → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54129018398900379363090206349 : (((p2 ∨ (((p4 → False) ∧ (p4 ∨ (True → p5))) ∧ p3)) → (((p4 → p4) → (p5 ∨ (True ∧ ((p3 ∧ p1) ∨ (p4 ∧ p4))))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354689619945549876745208747582 : (p5 → ((((True ∧ (p4 → (((p2 ∧ p3) ∧ ((p5 ∧ p4) ∨ ((p3 → p1) → ((True ∨ p3) ∧ p1)))) → p4))) → p4) ∨ (p4 ∨ False)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124302092793487008810756151939 : (((((p4 → False) ∨ (p3 ∨ p1)) ∨ (p2 → p3)) ∧ ((p1 ∨ (p5 ∧ (((p5 ∨ (False → True)) → (p4 → p4)) → False))) ∧ p2)) → (p4 ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h3.left
      let h7 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h3.left
        let h15 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h17.left
          let h19 := h17.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h3.left
        let h22 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h24.left
          let h26 := h24.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h3.left
    let h29 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h30 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148289566110333309754469732882 : ((((p4 → ((p4 → (True ∧ (p2 ∧ (p2 → (False → p5))))) ∧ p5)) ∨ (True ∨ p4)) → (p2 → (p5 → p2))) ∨ (p5 ∧ ((p5 ∧ p1) → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_382742247943732269377741495784 : ((((((False ∨ (p1 → p3)) → ((p2 ∨ p3) → (p5 → ((p2 → (((p4 ∨ (p3 ∨ False)) ∨ p2) ∧ (False ∨ p5))) ∧ p5)))) ∨ False) ∨ p4) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h15 =>
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h18 =>
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h21 =>
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65196071306278873127429206448 : ((p3 ∨ (((((p2 → ((True → p5) → (False ∨ p2))) → (((p2 ∧ (p4 → (p2 ∨ p4))) → (p5 ∨ p3)) ∧ p3)) ∨ p3) ∧ True) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53847960862530769339412476050 : ((((p4 ∨ (p3 ∨ (p5 → p2))) → ((p3 ∧ p2) ∧ p5)) ∨ ((True → ((False → (True ∨ ((False ∧ True) ∧ True))) ∧ p4)) → (p2 → p4))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178436667709581145623400712568 : ((((p3 → ((p4 → p5) → (p2 ∧ p2))) ∨ True) ∧ ((p2 → False) ∨ True)) ∨ ((((p4 ∨ ((p1 → p4) ∨ p4)) → p4) ∨ p2) → (p5 ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_113301051596101991148187149126 : (((((p5 ∨ p4) ∨ ((p4 → p4) → p5)) ∨ (p1 → (((True → (p1 ∧ p4)) ∧ True) → ((False ∧ p3) → False)))) ∧ (p1 ∧ p1)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781909486626381583868461213878 : (((p2 ∨ (p2 → ((p3 ∧ (p4 → ((p2 → p5) ∧ ((((False ∨ p2) ∧ (p2 ∧ True)) ∧ (False ∧ ((p1 ∨ p5) → p3))) → False)))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747981420993030686177444987797 : ((((p1 → True) → (p5 ∨ (p4 → (p1 → ((p4 ∧ (((True ∧ p3) ∧ (p4 ∨ ((p3 ∧ p1) ∧ (p4 ∨ (p3 ∧ False))))) ∧ p1)) ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315147070062388953109102918529 : (p3 ∨ (((p5 → ((p3 → True) ∧ False)) ∧ p2) → ((((False ∧ p4) ∧ p3) ∨ False) ∨ ((((p2 → False) ∨ False) ∨ (True → (p5 ∧ False))) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50309660670802169010366968410 : (((((((p4 ∧ (p2 → (p1 → p5))) ∨ True) → (p1 ∨ p2)) ∨ p5) ∨ ((p1 → p4) → (p1 → p4))) ∨ (((p2 → False) → p2) ∧ p4)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639260782811297772715317942480 : ((((((False → (p3 ∧ p5)) ∧ p5) → ((True ∧ (((False → (p3 → ((p5 ∨ p2) ∧ True))) ∨ (p5 ∨ p4)) ∨ p5)) → (True ∨ p3))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137400313092134765476519238241 : ((p3 ∧ (False ∨ ((((((True ∧ p4) ∧ (p5 ∧ p5)) → (p3 ∧ False)) ∧ False) ∨ p1) ∧ ((p1 ∧ p4) → (p3 → False))))) ∨ (True ∨ (p4 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134229037797112210809060333496 : ((((False ∨ (((p2 ∨ p1) ∨ True) ∨ p4)) → (p1 → (((p2 → p5) ∧ False) ∧ ((p4 ∧ (False → False)) ∨ p1)))) ∨ p2) ∨ ((p2 ∧ True) → p2)) := by
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
theorem thm_5_vars_336150188494170546502839697650 : (p1 → ((((((p1 → p3) ∨ p1) → ((p5 ∧ p5) → (((p1 ∧ ((True ∧ (p2 ∨ p2)) ∧ (False ∨ p1))) → p3) ∧ p3))) ∨ p1) → p3) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41231887969470632324741700493 : (((((p1 ∧ p1) → (True ∧ ((False ∧ p2) ∨ ((((p2 ∧ p4) → False) → p2) ∧ (p2 ∨ p5))))) ∧ (p1 → (False ∧ (p3 ∧ p3)))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65740131310242346340765509730 : ((p4 ∨ ((((((((p1 → p3) ∨ p1) → p5) ∧ p3) ∨ p1) ∨ (((p4 ∧ True) ∨ (p3 ∧ p2)) ∨ p5)) → p2) ∨ ((p5 ∧ p5) → True))) ∨ False) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45568862559279223578304965333 : (((p2 ∨ (True ∧ ((p1 → (p1 ∧ p1)) ∧ ((((((((p1 ∨ (p3 ∨ p1)) ∧ True) → p2) ∧ p4) ∧ False) ∨ p4) → p5) ∨ False)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347305748556673818332832248616 : (p3 → ((((False → (True ∨ (p3 ∨ (p1 ∨ p4)))) ∨ p1) ∨ p2) → (((p4 → ((p5 ∧ False) ∨ (True ∨ p5))) ∨ p1) ∨ ((p5 → p3) ∧ p1)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135660681520953930764687394039 : ((((p5 ∧ p5) → (((p2 ∨ p1) ∨ p1) → (((p4 → (p1 ∧ p4)) ∧ True) ∨ p4))) → (p1 ∧ (p4 → (p5 ∧ p5)))) ∨ ((True → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593868798575134038873189600586 : (((((((False ∨ (p1 → ((p4 ∧ p3) ∧ (False ∧ (((False ∨ p4) → p2) → p5))))) ∧ p3) → p2) ∨ (p1 ∧ ((p2 ∧ False) → p1))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158667540970046671974805775628 : ((p2 ∧ (((False ∨ (False ∧ ((p1 ∧ (p4 ∧ False)) → True))) ∨ ((p3 ∨ (False ∧ p2)) ∧ True)) ∧ True)) ∨ (((False ∨ p1) → True) ∨ (p1 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731607197361584483398540790156 : ((((p1 → (True ∨ p3)) → ((p1 → (p1 ∨ ((False → p3) ∨ p3))) → ((p1 ∨ True) → ((((p1 ∨ p5) ∧ False) ∨ p1) ∨ (False → p5))))) ∨ p3) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231532936510528491413248993172 : (((p4 → p4) ∨ True) → (((((p1 ∨ ((p2 ∧ True) → p4)) ∨ (p4 → ((p5 ∧ (p4 ∧ True)) ∧ (p1 ∧ p4)))) → False) → (p3 ∨ p4)) ∨ True)) := by
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
theorem thm_5_vars_200869442226193258974706852727 : ((False ∨ (((p3 ∧ (p5 → p5)) ∨ True) ∧ p2)) → ((((p4 ∧ p5) ∨ p5) ∧ False) ∨ (True ∧ (((p3 → p1) ∨ (True → True)) ∨ (p4 → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246096358373213054359039918932 : ((p4 ∧ p1) ∨ ((((p1 ∨ (p4 ∧ False)) ∧ p1) ∧ (p4 ∧ True)) ∨ ((False ∧ ((p2 ∧ ((True ∨ p5) → ((True → False) ∧ p4))) → p3)) → p1))) := by
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
theorem thm_5_vars_785672484672108928971157600848 : (((p4 ∨ ((((p3 ∧ (p3 ∧ p2)) → ((p4 → False) ∧ (p2 ∨ ((((True ∧ p2) ∧ (p1 → p5)) ∧ p2) → p4)))) ∨ (p4 → True)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136024622137281571230586628528 : ((((((False ∨ False) ∧ (False ∨ p3)) → p2) → (p2 → p5)) → (True → (((p4 ∧ p3) ∧ ((False ∨ p5) ∨ p1)) ∨ p4))) ∨ ((False ∧ p3) → p4)) := by
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
theorem thm_5_vars_205628925289849827876062315931 : (((p2 ∧ p3) ∨ (p4 ∨ (False ∨ p4))) ∨ ((((False ∨ ((p4 ∧ (((p1 ∧ p1) ∨ ((False ∨ False) ∨ False)) → True)) ∨ p1)) ∧ True) ∧ False) → False)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h3
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233453804775733227561005460034 : ((False ∨ (p2 → p3)) → ((((False ∨ (((False → ((False → (p1 ∨ False)) ∨ p1)) ∨ True) ∨ False)) → (p4 ∧ (p2 → True))) → p2) → (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3



