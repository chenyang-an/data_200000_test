variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171904712285406767629435223098 : (((False → ((((p5 → ((p1 → p5) ∨ (p2 ∧ True))) ∨ p2) ∨ True) ∨ p3)) → False) ∨ ((True ∨ ((True ∧ ((p4 ∧ p2) → True)) ∨ p4)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232444199730705589245125886794 : ((True ∧ (p5 ∧ True)) → ((((p3 → (p4 → p3)) → (False ∧ p1)) ∨ p5) ∨ ((p3 ∧ p2) ∨ (p1 ∨ (p4 ∨ ((p5 ∨ p4) → (p1 ∧ p1))))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_390255187922421359125379612268 : (((((p2 ∧ ((p2 ∨ ((p1 ∨ p1) ∨ (False → False))) ∧ True)) ∨ (((p4 → (p4 ∨ ((False → (p4 → True)) ∧ False))) ∧ p2) ∨ p5)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_265564134855107415158635834055 : (True ∧ (False ∨ (p3 → (p3 ∧ (((True ∧ False) → (p2 → ((((False → True) ∧ p5) ∧ False) → ((p3 → (p3 ∧ True)) → p4)))) → (p4 ∨ p3)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209169042645980111371960751386 : ((p3 ∨ (p5 ∨ (p5 ∨ (p3 ∧ p1)))) → (p2 ∨ (((((((p1 ∨ p5) ∨ (p4 → True)) ∧ (False → p2)) ∨ p3) ∨ p5) ∧ p1) ∨ (True ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682682527040105517588643393693 : (((((((p5 ∨ (True ∧ False)) → p1) ∧ p2) → (p3 ∧ ((p2 ∨ ((True ∨ p3) → p4)) ∨ p2))) ∧ (((p1 ∧ (p3 → p4)) ∨ p5) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112994605314523108706680020820 : (((p3 ∧ ((True ∧ ((True ∧ False) → p4)) ∨ (((((p5 ∧ p5) ∧ ((p2 ∧ True) ∧ True)) ∨ p2) ∨ (p1 ∧ True)) ∧ p4))) → p1) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135934492485962422026702434009 : ((((p1 ∧ ((p5 ∧ (False ∨ (True ∧ False))) → p2)) ∧ p1) ∧ ((((p2 ∨ p1) ∧ (p5 ∨ p1)) ∧ (p3 ∨ p1)) ∨ True)) ∨ ((p1 → True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57816793512581502373329617014 : (((p3 ∧ (True ∨ p2)) → (p1 ∨ (p1 → ((False ∨ ((p1 ∨ p4) ∧ ((True → (p4 ∧ (p3 → p2))) ∨ (p5 ∨ p1)))) ∨ (True ∧ p4))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216758108448777679056608058267 : ((((p2 → p2) → p4) ∧ p4) → (((((True ∨ p2) ∧ p1) ∨ p4) → (((((False ∧ (p5 ∧ p1)) ∨ (False ∨ False)) → False) → p2) ∨ p1)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158243170266989930519545101492 : ((((p1 → False) ∧ p3) ∨ ((p4 → ((True ∨ False) ∧ p2)) ∧ (False ∨ (True ∨ ((p3 → True) → p3))))) ∨ (p1 → (p4 ∨ (p5 → (p3 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55624936733234581382317227594 : (((p4 → (p1 ∨ ((p4 ∧ p2) → p3))) → (p2 → ((((True ∧ (p2 ∧ False)) ∨ (p1 → (p1 → (False ∨ (p3 ∨ p1))))) → p5) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147929779268624055774598793388 : ((((p4 → ((p1 → False) ∧ (p2 ∨ False))) ∧ (p3 ∨ (False ∧ (((True → False) ∨ p5) → p1)))) ∧ (p4 ∨ p5)) ∨ (True ∨ (False → (p5 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354763477351949157899561299690 : (p5 → (((p2 ∧ (p5 ∧ (((False ∧ (True ∨ p3)) → p3) → (p5 ∨ False)))) ∧ (((p3 ∨ (p4 ∧ p4)) ∨ False) ∨ ((False ∨ False) ∨ p5))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785811154482275859241079483953 : (((p4 ∨ ((True ∨ (p3 → ((p5 ∨ (((p5 → (p2 ∧ p1)) ∧ ((False → False) → (False → (p4 → (p1 → True))))) → p2)) ∧ False))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727175254147402395020164662568 : ((((True ∧ (p4 → False)) ∨ (p1 → ((((((p1 ∨ ((False ∧ False) ∨ p3)) → ((True ∨ (p2 → p3)) → False)) ∨ True) → False) → p2) ∨ True))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231787368337692745608632405777 : (((p4 ∧ False) → False) → (p2 ∨ ((((((p5 ∨ (False ∧ p2)) ∧ p5) ∧ ((p2 ∧ p2) ∨ p4)) ∨ (p1 ∨ (p1 ∧ True))) → p1) ∨ (False → False)))) := by
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
theorem thm_5_vars_118720749892113603541788470575 : ((p5 ∨ ((p4 → ((((((p5 → p2) → p3) → (False ∧ True)) ∨ ((False ∧ (p2 → p4)) → p2)) ∧ p2) ∧ True)) → (p2 ∨ False))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234035273138230623636905503798 : ((p5 ∨ (p1 → True)) → ((p5 → (((p4 ∨ True) ∧ ((p3 → p4) ∨ ((p2 ∨ (p2 ∧ p3)) → p1))) → (((p5 → p3) → False) → p4))) ∨ True)) := by
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
theorem thm_5_vars_41435915271870853187653816239 : ((((((p4 → (p1 → p1)) → p1) ∨ ((((p2 ∧ False) ∨ True) ∧ p2) ∧ False)) → (p5 ∧ ((True → p3) ∨ (False ∧ (True → p2))))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113773450733888130470913878012 : (((((p2 → (p3 → p5)) → p2) → ((p5 ∧ p5) ∧ (((p5 ∨ p1) ∧ True) ∨ (p1 → ((p1 → p2) ∨ p3))))) → (p3 ∨ p2)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246751221453218839036191610339 : ((p5 ∧ p5) ∨ ((((((False ∨ (p2 ∨ (p4 ∨ p3))) → False) ∨ (p3 ∨ p4)) ∧ (p3 ∨ False)) ∧ ((False → p3) ∨ (p2 → True))) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692878581113100841494387187017 : (((((False → (p3 ∨ p4)) → (((p1 → p5) ∧ p3) → ((True ∧ p5) ∨ p5))) ∧ (p5 ∨ (((p5 ∧ ((p3 ∧ False) → True)) → p2) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256720035755921197284578328979 : ((p1 ∨ p1) → ((((p2 → (p3 ∨ p3)) ∨ (p3 ∨ (p5 ∧ (p2 ∧ (p3 ∧ False))))) ∨ p1) ∨ ((p1 ∨ ((False → (True ∧ p3)) → True)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585306369367545269132874386537 : ((((((((p3 ∧ (((((p5 ∨ p3) → p4) ∧ (p5 ∨ (p1 → False))) → p5) → ((p1 → p2) ∧ p3))) → p2) ∨ True) ∧ False) ∧ False) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802069735560088024082691320466 : (((p2 → (True ∧ (((p3 ∨ (p5 → (p2 → (False ∨ True)))) ∨ ((p2 ∧ p5) ∧ (True → ((p5 ∧ True) → ((p1 ∨ p1) → False))))) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57931431178927987059041051865 : (((True → (False → p5)) → (p2 ∨ (p1 → (p3 ∧ (((p4 ∧ p2) ∨ ((((p2 → p4) → p1) ∧ p1) → (p5 ∧ (False ∧ True)))) → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216767908130634644058448953972 : ((((p5 → False) → p2) ∧ p2) → ((p3 → ((p4 ∧ ((False → p1) → p1)) ∨ ((p5 ∧ p4) → (((p5 ∧ p3) → False) → (True → p2))))) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87279045937626264863948336038 : ((((((False ∨ False) → True) → True) → False) ∧ (True → ((p1 → ((p4 ∧ ((p5 → (p4 ∧ p1)) → (p3 ∨ (p4 ∨ p1)))) → False)) ∨ p3))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((False ∨ False) → True) → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179381928890502964099761646301 : ((p3 ∨ ((False ∧ ((p4 ∨ False) ∨ (p1 ∧ (p1 ∨ (p5 ∧ True))))) ∧ p2)) ∨ (True ∨ (((p4 ∧ (p1 ∧ (p1 → p4))) ∨ (p1 → p3)) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314256008546124397274704339067 : (p3 ∨ ((((p4 ∧ p2) ∧ ((p2 ∧ False) ∧ p5)) ∧ (((p2 ∧ (p5 → True)) ∨ p3) ∨ ((p3 ∨ (True ∨ p3)) ∨ False))) ∨ (p2 → (False → False)))) := by
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
theorem thm_5_vars_311805729517400377913769326246 : (p2 ∨ (p1 ∨ (((False → p3) ∧ (((p4 → p4) → p5) ∨ (((((p4 ∨ p4) ∨ (False → True)) ∨ ((p5 → p3) ∧ p5)) ∨ False) ∧ True))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620943201200643149507342747433 : (((((p4 ∨ p3) → ((p2 ∨ (p4 ∧ (True → ((p3 → (p2 → (p4 ∨ p2))) ∧ (((p3 → p3) ∧ p3) ∨ (p3 ∨ True)))))) ∨ p3)) ∨ p1) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170239789943699123012115285177 : (((((p4 ∨ (p2 ∧ p1)) ∨ True) ∨ False) → (p3 ∨ (p4 → (p5 ∨ (False → p4))))) ∧ ((False → (p4 ∧ ((p2 → (p2 ∨ False)) ∧ p5))) ∨ p5)) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h5
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h6
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h16
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h16
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h17
  -- False on the left can always be used.
  apply False.elim h16
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181504792442981496075109088307 : ((p5 ∨ ((False ∨ False) ∨ (((True ∧ (p3 ∨ True)) ∨ False) → (True → p2)))) → ((True → (False ∨ (p2 → p5))) ∨ ((p5 ∨ (p2 ∧ p4)) → True))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- False on the left can always be used.
        apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40947384618036371447150813967 : ((((((p4 ∧ (p3 ∧ (p3 ∧ (((((True → True) → True) ∨ False) ∧ (p2 ∧ True)) ∨ p4)))) ∧ False) ∧ (p1 → p5)) ∨ (False ∨ p5)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196581913061760797969829673069 : ((p4 → ((p1 ∧ ((True ∨ p1) ∧ p2)) → p2)) ∧ ((True ∨ p2) → ((p1 ∧ ((((p4 ∧ p1) ∧ p4) ∧ p2) ∨ (p3 → p2))) ∨ (True ∨ p1)))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  -- Implications on the right can always be decomposed.
  intro h9
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180586746794660173844876384791 : (((p5 ∧ ((p4 ∧ (False ∨ p3)) → (p5 → p3))) → (False ∨ (p3 ∧ False))) → (((p1 ∧ (p4 ∧ (True ∨ p3))) → p2) → ((True → False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110719364375711537572613973962 : (((((False ∨ (((p4 ∧ ((p3 → (p2 ∧ p2)) → (True ∨ (p1 ∧ True)))) ∨ p1) → (p1 ∨ p5))) ∧ (p1 ∨ p5)) ∧ p4) ∧ p5) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152797452392056298385746590200 : (((p5 ∧ False) → ((True → True) ∧ ((((p2 ∧ p2) → (p4 ∧ p3)) → (p5 ∧ ((p4 ∧ p1) → p1))) ∨ p3))) → (p5 → ((p4 ∧ p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354202839813060685427027307567 : (p5 → (((p3 ∧ (p4 ∨ ((((p4 ∧ (p1 ∨ (True → p4))) ∨ p5) ∧ p5) ∧ ((p1 ∨ (p3 ∧ (True → p4))) ∧ (p4 ∨ p4))))) ∨ True) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761785365450427040850309710927 : (((p3 ∧ ((((p4 ∨ ((p2 ∨ (((True → (p2 → False)) ∧ (False → (p5 → p3))) ∨ False)) ∧ (p5 ∨ p4))) ∧ (p5 → True)) ∧ p5) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_853605497538522645472117478 : ((p2 ∨ ((p5 ∨ p3) ∧ (False ∨ (((p4 → p2) → True) → (((True ∨ (p2 ∨ p5)) → (p3 → (p2 ∨ (p2 ∨ True)))) → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300911088276121447132267063023 : (False ∨ (((p5 ∧ (p1 ∨ p5)) ∨ ((((p3 → p4) → True) → p5) → (p2 → p4))) → ((((False ∨ p5) → False) ∧ p1) → ((True → p3) ∨ p1)))) := by
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
  cases h1
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632491465056741994852312270680 : (((((p3 ∨ ((p2 → False) ∧ (True ∧ ((((p1 → True) → p2) ∧ p4) → (True → ((((p1 ∧ p2) ∧ p2) ∨ p3) ∨ True)))))) → p1) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135481489029543854509799106808 : ((((False → (p1 → (True → p5))) ∧ ((p5 → ((True ∧ p5) ∧ (p2 ∧ p4))) ∨ (True ∨ p4))) → ((p2 ∨ False) ∨ p2)) ∨ (True ∨ (p3 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801971785457543487485401045189 : (((p2 → ((p2 → p5) ∨ ((p4 ∨ ((True ∧ ((p4 ∧ ((p1 ∧ (p4 ∨ False)) ∨ ((p5 ∧ (p5 → p1)) → True))) ∨ p2)) ∧ True)) ∨ p1))) ∨ p5) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325698132969776121375807356904 : (p5 ∨ (p1 ∨ (((True ∨ (p4 ∨ (p4 ∨ (p2 ∧ p3)))) ∧ p1) → (False ∨ (False ∨ ((p2 ∧ ((True ∧ (p4 ∨ True)) ∧ (p1 → p1))) ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115864018819790261579247743027 : (((p2 → (True → (p2 ∨ False))) ∧ (((((p4 → ((True ∨ True) ∧ True)) → p1) ∨ p5) → (p5 ∨ ((p1 ∧ p2) ∨ p1))) → p4)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50596268505262604195723292170 : ((((p4 ∧ ((p5 ∨ (p1 → p5)) ∨ ((((p1 ∨ p5) ∧ p4) ∨ (p2 ∨ p2)) ∨ False))) ∧ (p3 → p1)) → ((False ∨ p4) ∨ (p4 ∧ True))) ∨ p4) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h14 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h15 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h13
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h18 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
    case inr h19 =>
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64108546113880997677719121253 : ((False ∨ ((p1 → ((p2 ∧ p3) ∨ (False ∧ (p4 ∧ p5)))) ∨ ((((False ∧ p2) ∨ ((p3 ∧ True) ∨ False)) → (p5 ∧ (False → False))) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307337313793298189050501887363 : (p1 ∨ (p3 ∨ ((p1 ∧ p5) → (p4 ∨ ((((p4 → (p3 ∧ (False ∨ p1))) ∧ (True ∨ p5)) ∨ ((p5 ∨ p2) ∧ True)) → ((p2 ∨ p3) ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52260760887281429224018837066 : (((p4 ∨ (((p3 ∧ (p5 ∨ (True ∨ ((True ∧ p5) ∨ (True → True))))) ∨ p4) ∧ p5)) → (p1 ∨ ((True ∨ (p4 ∧ p1)) → (p1 ∨ True)))) ∨ p2) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h17.left
          let h19 := h17.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h19
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h22
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h23 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h24 =>
            -- Conjunctions on the left can always be decomposed.
            let h25 := h24.left
            let h26 := h24.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h26
        case inr h27 =>
          -- Disjunctions on the left can always be decomposed.
          cases h27
          case inl h28 =>
            -- Conjunctions on the left can always be decomposed.
            let h29 := h28.left
            let h30 := h28.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h31
            -- Disjunctions on the left can always be decomposed.
            cases h31
            case inl h32 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h33 =>
              -- Conjunctions on the left can always be decomposed.
              let h34 := h33.left
              let h35 := h33.right
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h35
          case inr h36 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h37
            -- Disjunctions on the left can always be decomposed.
            cases h37
            case inl h38 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h39 =>
              -- Conjunctions on the left can always be decomposed.
              let h40 := h39.left
              let h41 := h39.right
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h41
    case inr h42 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h43
      -- Disjunctions on the left can always be decomposed.
      cases h43
      case inl h44 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h45 =>
        -- Conjunctions on the left can always be decomposed.
        let h46 := h45.left
        let h47 := h45.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h47



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218648807197813927398487540681 : ((True ∧ ((False ∨ p1) → p2)) → ((((((False → (((False ∧ p2) ∧ p1) ∨ p2)) ∨ p2) ∧ (True ∧ p1)) ∨ p1) ∨ p1) → ((p2 ∧ p2) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h6.left
        let h9 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h1.left
        let h11 := h1.right
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h12 : (False ∨ p1) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h13 := h11 h12
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h6.left
        let h16 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h1.left
        let h18 := h1.right
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h1.left
      let h21 := h1.right
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h22 : (False ∨ p1) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h23 := h21 h22
      -- One of the premise coincides with the conclusion.
      exact h23
  case inr h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h1.left
    let h26 := h1.right
    -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
    have h27 : (False ∨ p1) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h24
    -- We have shown the premise of h26, we can now drive its conclusion.
    let h28 := h26 h27
    -- One of the premise coincides with the conclusion.
    exact h28
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h29 =>
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h33 =>
        -- Conjunctions on the left can always be decomposed.
        let h34 := h32.left
        let h35 := h32.right
        -- Conjunctions on the left can always be decomposed.
        let h36 := h1.left
        let h37 := h1.right
        -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
        have h38 : (False ∨ p1) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h35
        -- We have shown the premise of h37, we can now drive its conclusion.
        let h39 := h37 h38
        -- One of the premise coincides with the conclusion.
        exact h39
      case inr h40 =>
        -- Conjunctions on the left can always be decomposed.
        let h41 := h32.left
        let h42 := h32.right
        -- Conjunctions on the left can always be decomposed.
        let h43 := h1.left
        let h44 := h1.right
        -- One of the premise coincides with the conclusion.
        exact h40
    case inr h45 =>
      -- Conjunctions on the left can always be decomposed.
      let h46 := h1.left
      let h47 := h1.right
      -- We want to use the implication h47 based on <expert-advice>. So we show its premise.
      have h48 : (False ∨ p1) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h45
      -- We have shown the premise of h47, we can now drive its conclusion.
      let h49 := h47 h48
      -- One of the premise coincides with the conclusion.
      exact h49
  case inr h50 =>
    -- Conjunctions on the left can always be decomposed.
    let h51 := h1.left
    let h52 := h1.right
    -- We want to use the implication h52 based on <expert-advice>. So we show its premise.
    have h53 : (False ∨ p1) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h50
    -- We have shown the premise of h52, we can now drive its conclusion.
    let h54 := h52 h53
    -- One of the premise coincides with the conclusion.
    exact h54
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h55 =>
    -- Disjunctions on the left can always be decomposed.
    cases h55
    case inl h56 =>
      -- Conjunctions on the left can always be decomposed.
      let h57 := h56.left
      let h58 := h56.right
      -- Disjunctions on the left can always be decomposed.
      cases h57
      case inl h59 =>
        -- Conjunctions on the left can always be decomposed.
        let h60 := h58.left
        let h61 := h58.right
        -- Conjunctions on the left can always be decomposed.
        let h62 := h1.left
        let h63 := h1.right
        -- We want to use the implication h63 based on <expert-advice>. So we show its premise.
        have h64 : (False ∨ p1) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h61
        -- We have shown the premise of h63, we can now drive its conclusion.
        let h65 := h63 h64
        -- One of the premise coincides with the conclusion.
        exact h65
      case inr h66 =>
        -- Conjunctions on the left can always be decomposed.
        let h67 := h58.left
        let h68 := h58.right
        -- Conjunctions on the left can always be decomposed.
        let h69 := h1.left
        let h70 := h1.right
        -- One of the premise coincides with the conclusion.
        exact h66
    case inr h71 =>
      -- Conjunctions on the left can always be decomposed.
      let h72 := h1.left
      let h73 := h1.right
      -- We want to use the implication h73 based on <expert-advice>. So we show its premise.
      have h74 : (False ∨ p1) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h71
      -- We have shown the premise of h73, we can now drive its conclusion.
      let h75 := h73 h74
      -- One of the premise coincides with the conclusion.
      exact h75
  case inr h76 =>
    -- Conjunctions on the left can always be decomposed.
    let h77 := h1.left
    let h78 := h1.right
    -- We want to use the implication h78 based on <expert-advice>. So we show its premise.
    have h79 : (False ∨ p1) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h76
    -- We have shown the premise of h78, we can now drive its conclusion.
    let h80 := h78 h79
    -- One of the premise coincides with the conclusion.
    exact h80



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63298784673050752165261802153 : ((p5 ∧ (((False ∨ p2) ∧ p2) → ((p2 ∨ (p5 ∨ (p4 ∨ (p3 → (p3 ∧ (True ∨ True)))))) → ((p5 → p1) ∨ (p1 ∨ (p5 → p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232293437343054689690127838532 : (((p3 → True) → False) → (p1 ∨ (((((p5 → (((p4 → p2) ∨ p5) ∧ (p1 ∧ True))) ∧ (p3 ∧ True)) → p1) ∧ (p3 ∨ (p3 → p3))) → p5))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1542296594825701625851880176 : ((False ∧ (((p3 ∧ ((p4 ∨ (p4 → (p5 → p3))) ∨ False)) ∨ p2) ∧ ((p3 ∨ (((True ∨ p4) ∧ p5) ∧ p4)) → p5))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309323910224673156548297311318 : (p2 ∨ ((((p5 ∨ (False ∨ (p2 ∨ p2))) ∨ (p1 ∨ ((p5 ∨ (p1 ∨ p2)) ∨ (p2 ∨ ((p5 ∧ (False ∧ p1)) ∨ True))))) → False) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343525678839321943582437601943 : (p2 → ((p4 ∧ p4) → ((p1 ∨ (False ∨ (p1 ∨ False))) → ((p2 → (p3 ∨ p3)) ∨ ((p2 ∧ (((p4 ∧ p3) ∧ (p5 → True)) ∧ p4)) ∨ True))))) := by
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
    let h5 := h2.left
    let h6 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h2.left
        let h12 := h2.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200948733647584496706489419467 : ((p2 ∨ (((p3 ∨ (p4 ∧ p2)) ∨ p4) ∨ p1)) → ((p3 ∨ (p2 ∧ p2)) ∨ ((True ∨ True) ∨ ((((p4 ∨ False) → p1) ∨ (False ∧ p4)) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h7 =>
          -- Conjunctions on the left can always be decomposed.
          let h8 := h7.left
          let h9 := h7.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166286384611449097220066653723 : ((p4 ∧ ((p1 → ((p2 ∨ (p4 ∧ ((p2 → (p2 ∨ True)) ∧ p2))) ∨ p2)) ∧ (p1 ∧ True))) ∨ (p3 → (True ∧ ((p4 → (p4 ∨ p3)) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618585370966029799028616894261 : (((((p3 ∨ (p5 ∨ (p3 → p5))) → (p2 → ((((True ∨ (p1 ∨ p5)) ∨ ((p3 ∧ p2) ∧ True)) → p5) ∧ (p2 → (False → p5))))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_213446083422488134895941943489 : (((p5 ∨ (True ∨ True)) ∧ p3) ∨ (((True ∨ (p5 ∧ p4)) → (p5 ∧ ((((p4 ∧ p2) ∧ p4) ∨ (False → p3)) → p5))) → (p3 → (p2 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ (p5 ∧ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634397311175379420846878225042 : (((((((((True ∨ False) ∧ True) → p5) → (p4 ∨ (p2 ∧ ((True ∨ p3) → (p2 ∨ (p5 → p4)))))) ∨ p4) ∧ ((p2 ∧ p3) → p4)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114989964971847450602901041449 : ((((((p2 → p2) ∧ ((p2 ∨ p1) ∨ p1)) ∧ True) ∧ (p5 ∨ False)) ∧ (((((p5 ∨ p2) ∧ True) ∨ p2) ∧ True) ∨ (True ∨ True))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654517641010051615474561631755 : (((((p2 ∧ (p4 ∨ ((((p2 ∧ ((p5 ∧ (p2 ∧ False)) ∧ p4)) ∨ (False ∨ (False → p3))) → (True ∧ p5)) → p4))) ∨ True) ∨ (p3 ∧ p5)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_136188587754867035108617926988 : (((((p5 ∨ p1) ∧ False) → (p3 ∨ True)) ∧ (p4 ∨ ((p5 ∨ ((((True → p4) ∨ p3) ∨ p1) ∧ (True ∨ p5))) ∧ p3))) ∨ ((p2 ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60637568095173211814146174719 : ((True ∧ ((((True ∧ ((((p4 ∨ p4) → (p3 → False)) ∨ (False ∧ p5)) ∧ (p1 ∨ p4))) ∨ (p2 ∧ p4)) ∧ False) ∨ ((True ∨ p2) ∨ p1))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318611588091576424784674198032 : (p4 ∨ (((p5 ∧ (p1 ∧ (p4 ∨ True))) → (p2 ∧ ((p2 ∧ ((p1 ∧ ((p1 ∨ (p1 ∨ (p3 ∧ p2))) ∨ True)) ∨ p3)) ∨ False))) ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245680806095441616554067755131 : ((p3 ∧ p1) ∨ ((True → p3) ∨ (p2 → ((p3 ∧ p4) ∨ ((False ∧ (((False ∧ (p5 → p4)) → (p2 ∧ p3)) ∨ (False ∨ (False ∧ p4)))) → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171978454240720918356626587938 : (((p5 ∨ (((p2 → p3) ∧ False) ∧ ((p1 ∧ p4) ∨ (False ∨ p3)))) ∧ (True → p4)) ∨ (p2 ∨ (True ∧ (p2 ∨ (((False ∨ p4) → p4) ∨ p4))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166218399812437184710342220005 : ((p2 ∧ (((((p3 ∧ p1) ∧ (p5 ∧ True)) → ((p5 ∨ p5) ∨ p4)) ∧ (p1 ∧ p1)) → True)) ∨ (((((False ∨ p2) ∧ p5) ∧ p5) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137171594965154659721234725461 : ((False ∧ ((((p5 ∧ (p5 ∧ p2)) ∨ True) → (((p5 ∨ False) → p2) ∨ (p4 ∨ (True ∧ p5)))) ∧ (p2 ∨ (p2 → p4)))) ∨ (p1 → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47893402627592679086387838751 : (((((p5 → (p4 → p1)) → ((p4 ∨ (False → (((p4 → p1) ∨ p1) ∨ (p3 ∨ False)))) → (p1 ∧ p2))) ∨ (True ∨ p3)) → (p2 ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260551174905892685544269031401 : ((p3 → p1) → ((True ∨ ((True ∨ (p2 ∧ True)) → p4)) ∧ ((p3 ∧ p4) ∨ (((p1 ∨ (p5 ∧ (p3 ∧ (p1 ∧ p1)))) ∧ (False ∨ p1)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_128425959710280876844483312841 : ((p4 → (p1 → (p4 → ((False ∧ ((False ∨ p3) ∨ (False ∨ p1))) → (p1 → ((p5 → p2) → ((p3 ∧ (False → True)) → True))))))) → (p2 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50167387330539459936819055612 : (((p5 → ((True → p5) → ((p3 ∨ p5) ∧ (p4 ∨ (p2 → (p4 → (p3 ∧ ((p3 → p4) ∧ p4)))))))) ∧ (((p5 ∨ p5) ∨ True) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134540786881687975791392388265 : ((((((p1 ∨ (p5 ∨ (p2 → (p1 ∧ False)))) ∨ (p3 ∨ (True ∨ (p4 → p5)))) → ((p4 → p2) ∨ p3)) → p5) → p2) ∨ (False → (p1 ∧ False))) := by
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
theorem thm_5_vars_161070222544805290111279423617 : (((p2 → (True → p5)) → ((((p1 ∧ ((p1 ∨ (p1 ∧ p4)) ∧ (False ∨ p2))) → p2) → p4) ∨ p1)) → ((p5 → ((p4 ∧ p5) ∨ p1)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p2 → (True → p5)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h3
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : ((p1 ∧ ((p1 ∨ (p1 ∧ p4)) ∧ (False ∨ p2))) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h15 =>
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- One of the premise coincides with the conclusion.
          exact h16
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h20 =>
          -- False on the left can always be used.
          apply False.elim h20
        case inr h21 =>
          -- One of the premise coincides with the conclusion.
          exact h21
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h22 := h7 h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h22
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h23 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184079856556539532542990672970 : (((((True ∨ p5) ∧ (False → p4)) → (p2 ∧ (p2 ∧ p5))) ∨ p4) ∨ (p2 → (((p5 → p4) ∨ p1) ∨ ((p3 → True) → (p2 → (True ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46965278257041513209601527559 : (((((((p4 ∧ (p2 → False)) ∨ (False → p1)) → (((True ∨ p4) → (((p2 ∧ p1) ∨ p2) ∧ p1)) ∧ p4)) ∨ p1) → p3) ∨ (True ∨ p1)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49394006581885876914641769782 : (((((((p1 → ((p4 ∧ False) ∨ False)) → (p1 ∧ ((False ∨ p3) ∧ False))) ∧ (p2 ∧ p3)) → (p1 ∨ p5)) ∧ p2) → (p5 → (p3 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694533627431010815077125009493 : ((((p1 ∧ (((p5 ∧ p2) ∧ ((True → False) ∨ (p2 → (p3 ∨ p5)))) ∨ False)) ∨ (False ∧ (((p4 ∨ p2) ∧ p1) ∧ ((p2 ∨ p1) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136545655344617895402515192163 : ((((p3 ∨ p1) ∧ p3) ∨ ((p4 ∧ (p4 ∧ (((p3 ∧ (p3 ∧ True)) ∨ p4) → ((p1 ∨ (p1 ∧ p2)) ∧ True)))) ∨ p4)) ∨ (p5 → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305757187305620184834797198375 : (p1 ∨ ((((True ∧ ((p3 ∧ False) ∨ p3)) ∧ True) ∧ p5) ∨ (((p1 ∧ True) ∨ (p1 → ((p4 → False) ∨ ((p3 ∨ p5) ∨ (p4 → p1))))) ∨ False))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213523484068160142764214800158 : (((p5 → (True ∨ p2)) ∧ p5) ∨ (p4 ∨ ((((False ∨ p1) ∧ p5) ∨ ((p1 ∨ (((False → p5) ∧ p2) ∧ (p3 → False))) ∨ (False ∧ p4))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670477443178801134004461611432 : (((((p1 ∨ p3) ∧ ((((p4 ∨ (p3 ∨ False)) → ((p4 → ((False ∨ p4) ∧ p5)) ∨ p5)) → p2) ∧ (p2 → True))) ∨ ((p2 → p2) ∨ p2)) ∨ p1) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177887324466858179210412532158 : ((((p4 ∧ ((((p5 ∧ (p3 ∧ p2)) ∧ True) → p3) ∨ p2)) → p3) ∨ True) ∨ (p5 ∨ (((p5 → p1) ∨ (False ∨ True)) → ((False ∨ p4) ∨ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55539830016392910202507587423 : (((True ∧ (p1 ∧ (p1 ∨ (p2 ∧ p4)))) → ((False ∧ p2) ∨ ((False ∧ (p5 ∨ ((((p1 ∧ (False ∨ p5)) → p2) ∧ p1) ∨ p4))) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184483552675773727855640933506 : (((((p4 ∨ p5) ∧ (False → (p5 ∨ p5))) → p5) ∨ (False ∨ p1)) ∨ ((((p4 ∨ p3) → p5) ∧ False) ∨ (((p1 → (False ∨ True)) → False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214741512753777326914576519757 : (((p3 ∧ p5) ∨ (p1 ∧ p4)) ∨ ((p2 ∨ (p3 ∧ (p1 ∨ p3))) → (p2 → (((p5 ∧ p5) ∨ p2) → (((True → (p5 ∧ False)) → p5) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h7
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h15 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h17 := h4 h16
      -- We need to get the right conjuct of h17 based on <expert-advice>.
      let h18 := h17.right
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h23 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h24 := h4 h23
        -- We need to get the right conjuct of h24 based on <expert-advice>.
        let h25 := h24.right
        -- False on the left can always be used.
        apply False.elim h25
      case inr h26 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h27 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h28 := h4 h27
        -- We need to get the right conjuct of h28 based on <expert-advice>.
        let h29 := h28.right
        -- False on the left can always be used.
        apply False.elim h29
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197059495983601834471366907870 : ((((p1 → False) ∨ (p4 → (p2 → p1))) ∨ p4) ∨ (((((p5 → p1) ∨ ((p3 ∧ (False → p5)) ∨ p5)) ∨ False) → (p5 ∨ False)) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654519136670670106251525283958 : (((((p3 ∧ ((True → (((p4 ∧ (False → (p1 → p5))) ∧ ((p4 → True) → (p2 ∧ p1))) ∧ (False ∨ p4))) ∧ False)) ∨ False) ∨ (False → p5)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_340227607950190294042292895798 : (p1 → (p5 → (((((p4 ∧ ((((p5 ∨ p1) ∧ (p5 ∨ (p2 ∧ p1))) ∨ True) → p2)) → False) ∨ p2) ∧ p2) ∨ (p3 → ((p2 ∨ p2) → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
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
theorem thm_5_vars_515146735821026020264886407004 : ((((True → False) ∨ ((p3 → False) → (((p3 ∧ (p3 ∧ p1)) ∨ p5) ∨ (False → ((p5 → ((p1 ∧ (p1 ∨ p4)) ∨ p4)) → (p2 ∨ p2)))))) ∧ True) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588284073626643893084128657870 : (((((((p4 → ((p1 → p5) ∨ p5)) ∧ p4) → (p2 → ((((p1 ∨ p5) → (p4 ∨ ((False → p2) → p5))) → p5) ∨ p2))) ∨ False) ∧ True) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782610917493526996869756916539 : (((p3 ∨ (((((((True → p5) ∧ ((p3 → p5) → p4)) ∧ (p5 → (p5 ∨ (p1 → (True ∧ True))))) ∧ (True ∨ True)) ∨ p5) ∧ p2) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_220945037961482924566656816606 : (((p1 ∧ p4) ∨ True) ∧ ((p5 → True) ∧ (p1 ∨ (((True ∨ (p2 ∨ False)) → (((p1 ∧ p2) ∨ (False ∧ p1)) ∨ False)) → (p1 ∨ (p2 ∨ p3)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ (p2 ∨ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172988763866901504205086496319 : ((p5 ∧ (((p1 ∧ (p5 → ((True ∨ False) ∧ False))) ∧ (False ∨ (True ∨ False))) ∨ p1)) ∨ (True ∨ (p4 ∧ (((False → (p3 ∨ False)) ∧ p4) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797701719596976172743305725464 : (((p1 → ((p3 ∧ (((p5 ∧ (p2 → False)) → True) ∨ (p3 ∨ (p1 → (False ∧ (p5 → (((p3 ∧ (p4 ∧ p2)) ∨ p4) ∧ False))))))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



