variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230326747227524699945715315342 : (((p2 ∨ True) ∧ p2) → ((((False ∧ p1) ∧ p4) → p5) → (((p2 → p2) ∧ ((p2 → p3) ∨ True)) ∨ (p2 ∧ (((p5 → True) → True) ∨ p2))))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156819359228591305179546143120 : (((p3 ∨ ((p2 → p5) ∧ (p4 ∧ (False ∨ (p1 → ((False → (p1 ∧ (p1 → True))) ∧ p1)))))) ∧ True) ∨ (p1 ∨ ((True → (p2 ∧ p1)) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703884314239325876439078016819 : ((((((p1 ∨ p4) ∧ ((p3 → p3) ∨ (p4 ∧ False))) ∨ True) → (False ∨ ((p1 ∨ p5) ∨ (((True ∧ p4) ∧ (p5 ∧ (p1 ∧ p5))) ∨ True)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- False on the left can always be used.
        apply False.elim h14
  case inr h15 =>
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
theorem thm_5_vars_226306295458799757217956384970 : (((p4 ∨ p5) ∨ p2) ∨ ((True → False) ∨ ((p1 → ((p5 → p1) ∨ False)) ∧ (p1 ∨ (((False ∧ (p1 ∧ (p3 ∨ True))) ∧ (p2 ∧ p2)) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2541898965935906338550636876 : (((p1 ∧ (p1 ∧ (False ∧ (p5 → p1)))) ∧ p1) ∨ (((((p2 ∨ (p5 ∨ p5)) → ((p3 → True) ∧ (p4 → True))) ∨ p2) ∧ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156945094558742205680515693983 : (((((p5 ∨ ((p2 ∨ ((((p2 ∨ p3) ∧ False) ∧ p2) → False)) → p5)) ∨ p3) → (p3 ∨ False)) ∨ False) ∨ ((((False ∧ p1) ∧ p4) ∧ p1) → False)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354585524642779571884094625196 : (p5 → ((((p2 ∨ p5) → ((p2 ∨ (p1 ∧ p2)) ∨ ((p3 → (p1 ∨ p1)) ∧ (True ∨ (((False ∧ p2) ∧ (p1 ∨ p3)) ∧ p1))))) ∧ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231364502383805712064903637240 : (((False → p2) ∨ True) → ((((p2 ∧ (p1 → (False → p5))) → ((True ∨ (p2 ∨ False)) ∧ p5)) → p4) ∨ (True ∨ (((p1 ∨ False) → True) ∧ p5)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225914522832733521512669174133 : (((p1 ∧ p5) ∨ p4) ∨ (p4 → ((p4 ∨ p1) → (((True ∧ ((False ∨ p3) ∧ (True ∨ (p3 ∧ (p4 ∨ ((p3 ∧ True) ∧ False)))))) ∨ True) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134224956439455788737267466436 : ((((p5 ∨ ((p2 ∨ (p5 ∧ False)) ∧ p1)) ∨ ((p1 ∧ False) → (((p2 ∧ (p4 → p1)) ∧ p2) ∧ (p4 → True)))) ∨ p5) ∨ ((p3 ∨ p1) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- False on the left can always be used.
  apply False.elim h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322351371280132598214081335694 : (p5 ∨ (((((p4 ∧ False) → p4) → ((((((p4 ∨ p3) ∨ p1) ∨ p2) ∧ (p4 ∨ p2)) ∧ (p2 → False)) ∧ p2)) ∧ (p2 ∨ (p4 ∨ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116420249373577388667415899086 : (((p3 ∨ (p1 → p1)) → (((((True ∧ p4) → p2) → ((p2 → p5) ∨ (p2 → False))) → p5) ∧ (((p2 → True) ∨ p5) ∨ p2))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113432722968633375307627689576 : (((((p1 ∨ (False ∧ ((p3 ∧ (p5 → (((p1 → (True ∨ p5)) → (p4 ∧ False)) ∧ True))) → True))) ∨ False) ∨ p5) ∨ (p2 ∨ True)) ∨ (True → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64084820969482002335773490220 : ((False ∨ ((((((p4 ∨ p2) ∧ (p2 → True)) ∧ p3) ∨ (p1 ∨ p5)) ∨ True) ∧ ((((p1 ∧ p5) ∧ False) → (p2 ∧ p3)) ∧ (p3 → p3)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h10
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137388818457171768890591990298 : ((p3 ∧ ((False → p4) ∧ ((p2 ∨ (((((True ∨ False) → p3) ∨ p3) ∨ (p2 ∨ p2)) → p1)) ∧ ((p3 ∧ p4) ∧ False)))) ∨ (True → (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254609669522744001707630414897 : ((p3 ∧ p1) → ((False → True) → ((((False ∨ p2) ∧ (p3 → ((True → ((False ∧ p4) ∧ p5)) ∨ (p2 → p1)))) → (p1 → False)) ∨ (p3 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67708377385651163101587393754 : ((p2 → (((((p3 ∧ (p3 → ((True ∧ (p3 → p1)) → (p3 ∧ (p4 ∨ p4))))) ∨ p2) ∨ (p1 ∧ ((p2 → p3) ∨ True))) ∧ p4) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605591967854934641992262633222 : ((((p4 → (((p3 ∨ (((p3 → ((p1 ∧ True) ∨ ((p3 ∨ p1) ∧ (p5 ∧ ((p4 ∨ False) ∧ p3))))) ∨ p1) → p4)) ∧ p1) ∨ p1)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184504635257086636664282709968 : ((((p3 ∧ p5) ∨ (((False ∨ p3) → p1) ∨ p5)) ∨ (p4 ∧ True)) ∨ ((((p4 ∨ ((p5 → True) ∧ (p3 ∨ p2))) → True) → (p3 ∨ True)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780715551726455046769542405196 : (((p2 ∨ ((False ∧ ((False ∧ p3) → (True ∧ p5))) ∧ (((p4 ∨ (False ∨ False)) ∧ (p2 → ((((p1 → p4) → p1) ∨ p5) ∨ True))) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_382904514247222262186136583009 : (((((True ∧ (((True → ((((p2 → True) ∨ p2) ∧ p2) ∧ True)) ∧ (((False ∨ ((p3 ∨ p2) ∨ p2)) ∧ p3) ∨ p2)) ∧ False)) ∨ True) ∨ p1) ∧ True) ∧ True) := by
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
theorem thm_5_vars_60238978486091072071225156319 : (((True → p5) → ((((((p2 ∨ p5) ∧ p5) → ((p3 → False) ∨ p5)) → False) → (((True ∨ p2) ∨ ((False ∨ p3) ∨ False)) ∧ p3)) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_389110956391576438390839144817 : (((((((p4 → ((p3 ∧ (p1 → p2)) ∨ (p2 ∧ (p3 ∧ True)))) ∨ p1) ∨ p4) ∧ (p5 ∨ (((p4 → p4) ∨ (p5 ∧ p3)) ∨ p1))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_114543979593067149334693103770 : ((((((p5 ∧ p1) ∨ ((((p1 → True) ∨ p3) ∧ True) ∧ (p3 ∨ p3))) ∨ True) ∧ p1) ∧ ((p3 ∧ ((p1 ∧ False) ∧ p4)) ∧ p2)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315025331933588886721203469087 : (p3 ∨ ((False ∧ (((p4 → p2) ∨ (p2 ∧ p1)) → p1)) ∨ (p5 → ((((((p4 → ((True → p2) → False)) → p4) → p4) ∨ p2) ∧ False) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327042953283571375192957847722 : (True → ((((True ∧ p5) → (((True → p2) → p4) ∧ p2)) ∧ (p3 ∨ (p2 → ((((True ∨ p5) ∧ p4) ∧ p1) ∨ ((False ∧ p2) ∨ p1))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54078989963199226142853236060 : ((((p4 ∨ True) ∧ (((True ∨ p2) ∨ p1) ∧ (False ∨ p1))) → ((False → ((((p2 ∨ (p3 ∨ p3)) → (False ∧ False)) ∧ p5) ∨ p1)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61064257575062018335858779581 : ((False ∧ (((((((False ∨ False) ∧ (((False ∧ p3) ∧ p3) ∧ p2)) ∨ (p4 ∨ True)) ∨ True) ∧ False) ∧ (p3 ∨ p1)) ∨ ((p5 → p3) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53503481052905570580575120225 : (((p2 ∨ (False → (((p5 ∧ ((p2 ∧ p4) → p3)) → False) ∨ False))) → ((True → (((p1 → (p5 ∧ p5)) ∨ (p1 ∧ False)) ∧ False)) ∨ True)) ∨ p2) := by
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
theorem thm_5_vars_56940615120825074351994855371 : (((False ∨ (p3 → True)) ∧ ((p1 ∨ (p5 ∨ (p1 ∧ p3))) ∧ (p5 ∨ ((p2 ∨ p2) ∨ (p2 → (p1 ∨ (p5 ∨ (p3 ∧ (False ∧ True))))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345595636166086686609351224669 : (p3 → (((p4 → False) ∧ (((p1 → False) ∧ p5) ∧ (((p5 ∧ (((p5 ∨ False) ∨ False) → p3)) ∧ (p3 → (p3 ∨ (False → p1)))) ∨ p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60116232192060730907800758074 : (((p3 ∨ p4) → ((((p5 → p1) ∧ (p1 ∧ ((True → False) ∧ (True ∧ ((p5 ∨ p3) → (p1 → (True ∨ p1))))))) ∨ False) ∨ (p4 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693122597420180239986301675747 : ((((p3 ∧ (p4 → ((False ∨ True) ∧ (False ∧ ((p5 → (p4 ∧ p3)) ∧ True))))) ∧ ((p3 ∨ (p2 ∧ ((p4 ∨ p5) → p2))) ∧ (False ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137751890059612098899763017486 : ((p2 ∨ ((((p4 ∧ p5) ∧ (p3 ∧ True)) ∨ (((((p4 ∧ ((True ∧ p5) ∧ False)) ∧ p3) ∨ True) ∨ p5) ∨ p1)) ∨ p4)) ∨ ((p1 ∧ False) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638210090670508108107593917896 : ((((((p1 → p4) ∨ (p4 ∨ (True ∧ (p3 ∨ p2)))) → (((p2 → p1) → False) ∧ (True ∨ (((True → p1) ∧ p5) ∨ (False ∧ p2))))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172769150328787662200607567036 : (((p1 ∨ False) → (((p1 ∨ p5) ∨ p3) → (p5 ∨ ((p2 → p1) → (p5 ∧ p5))))) ∨ ((p1 ∧ p4) ∨ ((p2 ∧ (p4 → p2)) → (p2 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323715441703249109529687271582 : (p5 ∨ (((((p3 → True) ∨ ((p4 ∨ p5) ∧ False)) → p4) ∧ ((p3 → (p3 ∧ p4)) ∨ ((p2 ∨ p3) ∧ p1))) → ((p4 ∨ False) ∨ (p4 ∨ p2)))) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((p3 → True) ∨ ((p4 ∨ p5) ∧ False)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h13 : ((p3 → True) ∨ ((p4 ∨ p5) ∧ False)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h14
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h15 := h2 h13
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153398482861507982056096776155 : ((p3 ∨ ((((False → (True ∧ True)) → True) ∧ (True → (p3 → p3))) ∧ (True ∨ ((p4 ∧ (False → p3)) ∧ p3)))) → (((p5 ∧ p4) → p1) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54873133323340375692921655873 : ((((False → ((p2 → p4) ∧ False)) ∧ p3) ∧ (p3 ∧ (((False ∧ p1) ∨ (((False ∨ (p2 ∧ p1)) ∨ p1) ∧ ((False ∨ p5) ∨ p5))) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165139060769432320397657972547 : (((((True ∨ ((True ∨ p4) → p4)) → ((p3 ∨ (p2 ∧ False)) ∨ p1)) → p3) ∧ (p3 ∧ True)) ∨ ((True → (p4 ∧ ((p4 ∧ p4) ∨ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180616345277083933738205645681 : ((((p5 ∧ False) → ((p2 ∨ False) → p5)) ∧ (p3 ∨ (p2 ∧ (p2 → False)))) → ((((False ∧ (p5 ∨ (p1 → (True → False)))) → True) → p3) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123486752942323435253576956260 : ((((((p1 ∨ ((p5 → False) → p1)) → (((True → p3) ∧ p3) ∨ p1)) → True) → False) ∧ ((p4 ∨ ((p5 ∧ True) ∨ p3)) ∧ p3)) → (p1 ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : (((p1 ∨ ((p5 → False) → p1)) → (((True → p3) ∧ p3) ∨ p1)) → True) := by
        -- Implications on the right can always be decomposed.
        intro h12
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h13 := h2 h11
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : (((p1 ∨ ((p5 → False) → p1)) → (((True → p3) ∧ p3) ∨ p1)) → True) := by
        -- Implications on the right can always be decomposed.
        intro h16
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h17 := h2 h15
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47031281311044841141155846232 : (((((((((False → (p3 ∧ p1)) → p3) → ((((p5 ∧ p3) ∨ p4) ∨ True) ∨ False)) → p2) ∧ p5) ∧ True) ∧ (True → p4)) ∨ (p5 → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86590140544952524256593593881 : (((((p3 ∨ p3) ∨ ((p2 ∨ True) ∧ True)) → False) ∧ ((p4 ∨ p2) ∨ (((False ∧ p3) ∧ ((p5 → False) ∧ ((p2 → p5) ∨ p4))) ∧ True))) → p5) := by
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
      have h6 : ((p3 ∨ p3) ∨ ((p2 ∨ True) ∧ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h9 : ((p3 ∨ p3) ∨ ((p2 ∨ True) ∧ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h9
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145104574808952585454984903340 : (((((((p3 → p4) ∧ p2) → p5) ∨ (p2 ∨ p3)) ∧ False) ∨ ((p2 → (True ∨ p2)) ∨ (False ∧ (p3 → p3)))) ∧ (True → (False → (True ∨ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136173367757867638413424984049 : ((((p4 → (p1 ∧ (p3 ∨ p1))) ∧ p5) ∧ (p5 ∧ (True → (p4 ∧ ((p4 → p5) → ((p1 ∨ (p1 → True)) ∧ True)))))) ∨ (p1 → (p1 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53093119113824577246845007790 : (((p2 ∨ ((p2 → p5) ∨ ((p2 → p4) ∧ (False ∧ (p2 ∧ False))))) ∧ ((p5 ∧ (((p3 → p4) → (p3 ∧ p2)) ∧ (p1 → p5))) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350324091538481838885731525251 : (p4 → ((True → ((False → False) ∧ (p5 ∨ (p4 ∧ ((p4 ∧ (((p1 ∧ False) ∨ (True ∨ p5)) ∧ p4)) → ((p3 → (p4 ∧ p5)) → False)))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199828098023953565161290355814 : ((((p5 → p4) ∧ (False ∨ p2)) ∧ (p1 ∨ True)) → (((((p3 → ((True ∧ False) ∧ p5)) ∨ (p2 → (False ∧ False))) → p1) ∨ p1) ∨ (p5 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h11 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h12 := h4 h11
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191512780263141923019958811811 : ((False ∧ (((True ∨ p4) ∨ (p2 → p4)) → (p3 ∨ p5))) ∨ ((p5 → False) → ((((p3 ∧ p1) → p3) ∨ p2) ∨ (((p2 ∨ p5) ∨ p3) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53888064921077893264972477732 : (((True ∧ (((p2 ∧ (p1 → p3)) ∨ p1) ∧ (p3 → True))) ∨ (((((False → p2) ∧ p4) ∧ (((True ∨ p1) ∧ p2) ∧ p3)) ∧ p4) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180393572395241924419073948536 : (((True ∧ (p4 → (((p5 ∧ p3) ∧ p4) ∧ (p3 → True)))) ∨ (p5 → p2)) → ((p4 → p4) ∧ (((p3 ∨ (True ∨ p3)) ∧ p2) → (True ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h20 =>
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h25 =>
        -- One of the premise coincides with the conclusion.
        exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110926015895265468893310940601 : ((((p4 → (p2 ∧ (p5 → (False → (p2 → ((((p5 ∨ ((p4 → p5) → p2)) ∨ p1) ∧ True) ∨ (False → p5))))))) → False) ∧ p4) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135502853969297595498614953620 : (((False ∨ (p2 ∨ (False → (((((p5 ∧ p1) → ((p4 → p3) → False)) → p5) ∧ p1) → p4)))) → (p1 ∨ (True ∧ p1))) ∨ ((p5 ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314419230949718097394048291423 : (p3 ∨ (((p4 ∨ (True → ((False ∨ (p4 ∨ True)) → (True ∨ (p4 ∧ (p1 ∧ p5)))))) → (p3 ∧ (p3 → p5))) ∨ ((True ∨ (p1 → p1)) ∨ p2))) := by
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
theorem thm_5_vars_168457748332681863877082342402 : (((p2 → p3) → ((p2 ∨ (p3 ∨ p4)) → (p2 ∧ (p5 ∧ ((True ∨ (p2 → True)) ∨ p2))))) → ((p5 ∨ (p4 → (p1 ∧ False))) ∨ (True ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246639213486592590813022673492 : ((p5 ∧ p3) ∨ ((p1 ∨ ((((True ∨ p4) ∧ (((p5 → p4) ∨ p1) → p3)) ∨ p3) ∧ p4)) ∨ (((p1 → ((False ∧ True) ∧ True)) ∧ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206945000079519173305562734456 : (((((p4 ∧ True) ∨ p5) → p4) ∧ p1) → (((((True ∨ p1) ∨ (((p1 → p1) ∧ p3) → p2)) ∧ (p2 → p5)) ∨ False) ∨ ((p4 ∨ True) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765230916597334960660831818987 : (((p4 ∧ (((p3 → (p2 ∨ True)) ∨ (((False ∧ (p2 → ((False ∨ False) → p1))) ∨ p1) → (p3 ∨ ((p3 ∨ p5) ∨ True)))) → (p2 ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58643181267622596828786965712 : (((p1 → p1) ∧ ((((p2 → (p5 ∧ p3)) ∧ p4) ∧ (((p4 ∧ (((p1 ∧ p4) → p5) ∧ (p3 ∨ p2))) ∧ p3) → p2)) → (p5 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136357549342874513972527050844 : (((((p5 ∧ p4) ∨ False) ∧ p5) ∨ (p4 ∨ (((p1 → (p4 ∧ (p2 ∨ p4))) → True) ∨ (p1 → (p1 → (True → p1)))))) ∨ ((p4 → p5) ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764890377767731177503955211308 : (((p4 ∧ ((((p2 → (p2 ∨ (p4 ∨ (p2 → (p1 ∧ p5))))) ∨ p5) ∨ (p1 → (((False → (p5 ∨ False)) → p1) ∧ (p2 → True)))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135075161720419308994257310085 : ((((((p1 → (True ∨ ((p3 ∧ p3) → (p4 → False)))) → (p4 ∧ p1)) ∧ (True ∨ p3)) → (p4 → p2)) ∨ (p5 → p4)) ∨ ((p2 → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141109021891817279692820223181 : (((((p5 → p3) → p3) → (p2 ∧ (p5 ∧ p5))) → (p1 ∨ (p3 ∧ (p5 → (p3 ∨ (p4 ∧ ((p5 ∧ p2) ∨ p2))))))) → (p3 → (p3 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125596847727867219361528252930 : (((p5 → True) ∧ ((((p5 ∨ p5) ∧ ((p4 ∧ p3) → ((((p2 ∧ p4) ∧ ((True → p5) ∨ p5)) ∧ p2) ∨ True))) → p1) ∨ p1)) → (p1 → p1)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60801182481694728226924218525 : ((True ∧ (p1 ∧ ((((True ∨ (p4 ∧ p3)) ∨ (True → p4)) ∧ p4) ∨ ((True → p3) ∧ ((True ∧ (p5 ∨ p4)) ∨ (p5 → (True ∧ p4))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187471223957517544507824751488 : ((True ∨ (p1 → ((p2 ∧ (False ∧ (True → p2))) ∧ (True ∧ False)))) → ((((True ∨ (p4 → (p2 ∨ p2))) ∨ (p2 ∧ p5)) → (False ∧ p3)) ∨ True)) := by
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
theorem thm_5_vars_148242498238254562145803383253 : ((((((p3 → (False → False)) → p1) ∨ p1) ∧ ((p5 ∧ (p1 ∧ False)) ∨ (False ∧ False))) ∨ ((p2 → p2) ∨ p1)) ∨ (p5 ∨ ((p2 → p4) → p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699821297167457418181718368879 : (((((((p5 ∨ p3) → (True ∨ p3)) → (True → True)) → (False ∧ False)) → ((((((True ∧ (p4 ∨ p3)) ∨ False) ∧ p3) ∧ p3) ∨ p5) ∧ p4)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∨ p3) → (True ∨ p3)) → (True → True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (((p5 ∨ p3) → (True ∨ p3)) → (True → True)) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h7
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172001182686888475712847702226 : (((((True → ((True ∧ True) ∧ p2)) ∧ ((p5 ∧ True) → False)) → p1) ∨ (p3 ∨ p3)) ∨ ((True ∨ p4) ∨ (True ∨ ((False ∨ p5) ∧ (True ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199116640040075899338096008527 : ((((p1 → (False ∨ True)) ∨ (p4 ∧ False)) ∧ p3) → (p1 ∨ (((((p1 ∨ p2) ∨ (True ∧ False)) ∧ p4) ∨ (p3 → (True ∨ False))) ∨ (p3 ∧ p4)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719327160128864461632052783426 : ((((p5 ∧ (p3 ∧ (p3 ∨ p3))) ∨ (((p4 → p4) ∨ ((((p1 ∧ p2) ∨ p5) ∧ False) ∧ (p1 → True))) → (p5 ∨ (False → (p1 → p3))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358701188325815344543175567560 : (p5 → (p5 → (((((p2 ∧ ((p2 ∧ p2) ∨ ((False ∧ p1) → ((p2 → (p1 ∨ p2)) → (p1 ∨ p4))))) ∧ p4) ∧ (p4 ∨ False)) ∨ p5) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313935855039805779461394434346 : (p3 ∨ (((((p4 ∧ (p3 → p3)) ∨ p2) ∨ (((p4 ∧ p2) ∨ p2) ∨ (p1 ∨ (p2 → (False ∨ (True ∧ (p4 ∨ p2))))))) ∨ p3) ∨ (True → p2))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247988137166441647226081635546 : ((p1 ∨ p4) ∨ ((p1 ∨ p1) ∨ (p5 ∨ ((p4 ∨ ((((p3 ∧ (p5 → p5)) ∨ ((p3 ∧ p4) ∨ p3)) → (p2 ∧ (p3 ∧ False))) → p3)) ∨ True)))) := by
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
theorem thm_5_vars_708888975218171982176893535837 : ((((((False ∧ (p4 ∧ False)) ∧ p5) ∨ (p2 ∧ p3)) → ((p5 ∧ ((p4 → (p2 ∨ True)) → ((p1 → False) ∧ (p1 ∧ (p3 ∨ p4))))) ∨ p3)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49767052640895748506936870842 : (((p1 ∨ (((((((True ∨ p2) → (False ∨ p5)) → p4) ∨ p2) ∧ ((p3 ∨ (p2 ∧ p3)) → p1)) → p3) ∧ p5)) → (False ∧ (p1 → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191867347087429251115039467857 : ((p4 ∨ (((p2 ∨ p4) → (p3 ∧ False)) ∧ (p4 ∨ False))) ∨ ((p5 ∧ (False ∨ p5)) → ((p1 → (((p5 ∧ p3) ∨ (p1 ∧ p4)) → True)) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48015671913250799471808524829 : ((((p3 ∨ ((p2 ∧ (p4 ∨ (((p1 ∧ p4) ∨ p1) ∨ True))) → False)) ∧ (((p4 ∧ p5) → (False → p4)) ∧ (False ∨ p3))) → (p1 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355631283577049809945819043274 : (p5 → ((p4 ∨ (p4 ∨ (((p5 → (((p5 ∧ p5) ∨ p3) → (p2 → (False ∨ (((p1 ∨ p1) → True) ∨ False))))) ∧ p1) ∨ p3))) ∨ (p5 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314870102703957567224400458787 : (p3 ∨ (((p2 ∨ True) ∨ (p1 → (p4 ∨ (p4 ∨ ((p5 ∧ p3) ∧ p1))))) → (p3 ∨ (p3 ∨ (False → (True ∨ ((True → (p2 ∧ p2)) ∨ p4))))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310385256436841470120669506878 : (p2 ∨ (((((p2 ∨ p3) ∨ p1) → (p3 ∨ p2)) ∨ p1) ∨ (((False ∧ (p2 → p5)) ∨ ((p3 ∧ p1) ∧ (p5 → ((True → p4) ∨ True)))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698558523214986322075616098523 : (((((p3 ∨ (p2 ∧ (True → p4))) ∨ (p3 → (p3 ∧ (p2 ∧ p2)))) ∨ (p5 → (((False ∧ (p4 → p2)) ∧ p4) ∨ (p1 ∧ (False ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131715526447060120913433167163 : (((p5 ∨ (p3 ∨ True)) → ((p5 ∧ p3) ∨ ((False ∨ (((p3 → p5) ∨ p5) ∨ (p4 ∧ (False ∨ (p5 ∨ p2))))) ∨ True))) ∧ (p5 ∨ (True ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678778194664410926544866800862 : (((((p5 → p2) → (((((True ∨ p1) → p3) ∨ False) → p2) → (p3 ∨ (p3 ∨ ((p4 ∨ False) → p4))))) ∨ (((p3 ∧ p2) ∧ p5) → False)) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358218355911540777993244215002 : (p5 → (p4 ∨ (((p2 ∨ p3) ∧ (p4 ∨ (((((((p2 ∨ True) → (p2 ∧ (p4 ∨ (p5 ∧ p1)))) ∨ p2) ∨ p4) ∨ p4) ∧ p2) → False))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54355450837486639184682913526 : (((p3 ∨ (((p4 ∨ (False ∨ False)) ∧ p2) ∨ p3)) ∧ (((True ∧ False) ∨ p2) ∨ (p2 ∨ ((p3 → (((True → True) ∨ p4) → True)) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314754849007657816087678477204 : (p3 ∨ ((p1 ∧ (((p3 ∧ p4) ∧ (p3 → p4)) ∧ (p1 ∨ (p1 ∧ (p4 → p5))))) ∨ ((p2 → ((p3 → (True ∨ (True ∧ p3))) ∧ p2)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204904772435262884555284527056 : ((((p2 → p3) ∧ (False ∨ p2)) → p1) ∨ ((((p5 → False) ∧ False) ∨ p5) ∨ (((p5 ∨ p3) → (True → p1)) ∨ (p3 → (p1 → (p3 ∨ p4)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171816203776671882973556604795 : ((((False ∧ (((p2 ∧ True) ∧ p5) → p2)) → ((p2 ∧ (p3 → p2)) ∨ p5)) → False) ∨ ((False ∨ (True → ((True ∨ p2) ∨ p1))) ∧ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113588055988552257694238707392 : (((p3 ∧ (p4 ∧ (p2 ∧ ((p5 ∨ (p2 ∧ p5)) ∨ ((p4 → p1) ∧ ((p1 → (False → p3)) ∨ (False ∨ False))))))) ∨ (p4 → p4)) ∨ (p3 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148161740392051373254925720365 : (((p5 → ((p5 → (p4 ∧ (True ∨ p1))) ∨ (p5 ∨ (p4 ∨ (p3 ∧ ((p4 → p1) → False)))))) → (p1 ∨ False)) ∨ (p3 ∨ (p1 ∨ (True ∨ p1)))) := by
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
theorem thm_5_vars_64531386663897550542160321840 : ((p1 ∨ (((p3 → ((p1 ∨ (p4 ∧ p5)) ∨ p2)) ∨ p3) ∨ ((False ∧ False) → ((False ∨ (p2 ∧ p3)) ∨ (p2 ∨ ((False ∨ p5) → p4)))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_42314323303429756900609429121 : (((p2 ∧ ((p2 ∧ p3) ∧ (((False ∧ False) ∧ (((p2 → p3) → (p2 ∧ p2)) → (p3 ∨ True))) ∨ (p3 ∨ ((p3 ∨ p4) ∧ p4))))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356063731548742207852559049369 : (p5 → ((((p5 → ((p3 ∨ ((p3 ∨ p5) ∧ (((p5 ∨ (p4 ∨ p1)) ∧ True) → p2))) ∨ p5)) ∨ False) → False) → (((False ∧ p2) → False) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 → ((p3 ∨ ((p3 ∨ p5) ∧ (((p5 ∨ (p4 ∨ p1)) ∧ True) → p2))) ∨ p5)) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738481255137374022516973420144 : ((((p1 ∧ p3) ∨ ((p5 ∧ ((p1 ∨ (False ∨ p2)) → p4)) ∨ (((((p5 ∧ p5) ∨ False) ∧ (((p5 ∧ p4) ∨ p3) ∨ False)) ∧ p3) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183697925345834910874468801609 : ((p3 → ((p5 ∨ p1) → ((True ∨ p1) → (p4 ∨ (True ∧ True))))) ∧ (p5 → (((p2 → p1) ∧ (False ∨ p1)) ∨ ((True → p5) ∧ (p5 ∧ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
  -- Implications on the right can always be decomposed.
  intro h10
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h11
  -- One of the premise coincides with the conclusion.
  exact h10
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626696025877034314286364317402 : ((((p5 → (((((p4 → (((False ∧ p1) ∧ False) ∨ (p1 → p3))) ∨ ((True → ((p1 ∨ p3) → p2)) ∨ p3)) ∨ p2) ∧ p4) ∨ p3)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218783086380159788884754480533 : ((p1 ∧ ((p4 ∨ False) → p2)) → (((((((p5 ∨ p4) ∧ ((p2 ∧ ((p1 ∧ p1) ∨ p1)) ∨ p2)) → p5) ∨ p3) ∨ False) ∨ True) ∨ (p3 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206167118899270090823939012051 : ((p5 ∧ ((p2 ∧ p1) ∧ (p4 ∨ p4))) ∨ (((p4 ∧ False) ∨ ((True → (False ∧ True)) → p5)) ∨ (((p5 ∨ ((p5 ∨ p2) ∨ p5)) ∧ p2) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



