variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42705420188586027141261303827 : (((p5 ∨ ((p3 ∧ (p4 ∨ (True ∧ True))) ∨ (p4 ∨ (False ∨ (((((p4 → p3) → (True ∧ (p5 → True))) → p1) ∧ p2) → True))))) ∨ p3) ∨ p4) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299239323709730852761738618712 : (False ∨ ((((((((p1 ∧ p3) ∨ False) ∨ p1) ∧ (((p5 ∨ p1) → p2) → p5)) ∨ (True ∨ (p5 ∧ True))) ∨ p3) ∨ (False ∧ (p3 ∨ p3))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65370519238647683797197067467 : ((p3 ∨ (((p4 ∨ p2) ∧ (p1 ∨ ((p5 → p5) ∧ (p4 ∧ p5)))) ∧ ((p3 ∨ p3) ∧ (((True ∧ (p2 → p4)) ∨ (p2 ∨ p1)) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118327240053103197255142663727 : ((p2 ∨ (((p2 → (p1 ∨ (p1 → (((((p2 → p1) ∨ (p4 ∨ False)) ∨ p5) → ((p4 ∧ True) ∧ True)) ∨ p2)))) → False) ∧ p1)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158555913898026615538446491099 : ((True ∧ ((((p2 → p1) ∧ p3) → (p2 ∧ (p4 ∧ ((p1 ∨ p3) ∨ (p4 ∨ (p5 ∨ True)))))) ∧ True)) ∨ ((True ∧ p3) → ((p1 ∨ p2) → p3))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37529681431833936794504153763 : ((((p1 ∧ ((p4 ∨ p1) ∨ ((p5 ∨ (False ∧ (p2 → (p5 ∨ (((True ∧ False) ∧ (p2 → p2)) ∨ (True ∧ p5)))))) ∧ p5))) ∨ p1) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164823943703557300507093337692 : ((((True ∨ p4) → (((((p5 → (p4 ∨ False)) ∧ False) ∨ False) ∨ p1) ∨ (p1 → p3))) ∨ p3) ∨ (((p1 ∨ (p5 → False)) → True) ∨ (p5 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669551431090897221611661242361 : (((((p5 → ((p3 ∧ ((False → p5) → False)) ∨ ((True ∧ p4) ∨ (True → ((p2 ∨ p5) → p3))))) → (p3 → p4)) ∨ ((p5 → p1) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185882121487044798921035887000 : ((((p5 → (((p1 → p2) → (p4 ∨ True)) ∧ False)) → True) ∧ p3) → ((p5 → False) → ((((p3 ∧ p2) ∧ p3) ∨ ((True → p3) → p3)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64182559528055222506436581097 : ((False ∨ ((p2 ∨ p5) → (((((p2 ∧ (False → p4)) → ((p1 ∨ p1) ∨ (p3 ∧ (True ∨ p1)))) ∧ (p4 ∧ True)) ∨ (False → p2)) ∨ True))) ∨ False) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322406831948902568945713770975 : (p5 ∨ (((((((True → False) → p1) ∨ (False ∨ False)) ∧ p4) ∧ (p4 → p1)) → (((p4 → p5) ∧ p3) ∨ (p5 ∨ ((p3 → p3) ∨ p5)))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h4
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614718433950356379937339704924 : ((((((((((p3 ∧ ((p5 ∧ p5) ∨ True)) ∧ False) ∨ (p1 ∧ True)) ∧ p2) ∧ False) ∧ (p2 ∧ p3)) ∨ (p1 → (True ∨ (p1 → p5)))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670424510768506085362874294660 : (((((p2 ∨ (p2 ∧ p4)) → ((p4 ∧ (p5 ∨ p4)) ∧ (p2 → ((p1 → True) → ((True → True) ∧ (True → p1)))))) ∨ (p3 ∧ (p4 → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56401798554758191238877485245 : ((((False ∨ (True ∧ p1)) → True) → (p2 → ((p5 ∨ p2) ∧ ((p5 ∧ p1) → ((((p3 → p2) → p2) → p4) ∨ (True ∧ (p1 ∨ True))))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69043625509918368726441951452 : ((p5 → (((True → ((False ∧ False) → (True ∨ p1))) → ((p1 ∧ (((p4 → p5) → (True → False)) → (p3 ∧ (p5 ∧ p4)))) ∧ False)) ∨ p5)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749919781079410555005422145367 : (((True ∧ (((p2 ∧ ((p5 ∨ (p5 ∧ ((p4 → (p3 → True)) ∨ (False → (((p4 ∧ p4) ∨ p2) ∨ p1))))) ∧ (p5 → p5))) ∨ p2) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314421720108841261071982033810 : (p3 ∨ ((((p4 → ((False ∨ (False ∨ p4)) → False)) → (p3 → p4)) ∨ ((((False ∨ p3) ∧ True) → p2) ∨ p4)) ∨ (p5 ∨ (False → (p3 ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45476594190288674194919786726 : (((False ∨ (((False → p1) ∧ ((p3 → (p5 → (p3 → ((p5 ∧ p5) → (p2 ∧ True))))) ∧ (p2 → p3))) ∨ ((p2 ∧ False) ∨ p1))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173788248367194846726871890869 : ((((p2 ∨ True) → (True ∧ ((((p2 ∧ p3) → p3) ∧ (p2 ∧ p4)) ∨ p2))) ∨ True) → (p4 → ((p5 ∧ (p1 ∨ (True ∧ (p1 → False)))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642055858173395431460062994542 : ((((True ∧ (((p5 ∨ (p3 ∧ (p2 → p5))) ∨ (((p5 → (p1 → p3)) ∨ ((True ∨ (p2 → (p2 ∨ False))) ∧ p3)) ∨ p2)) → p3)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752472366601627412192029734737 : (((False ∧ ((((p1 ∧ p3) ∨ p3) → ((((p1 ∧ (p2 ∧ (p4 ∨ True))) → (True → ((False ∧ p4) ∧ False))) → p3) ∧ (p2 ∧ p2))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147889793910511529979000017952 : ((((p3 ∨ (((((p2 ∨ True) ∧ p4) ∧ p5) → ((p1 ∨ False) ∨ p3)) ∨ (True ∨ p1))) ∧ p5) ∧ (p2 → p1)) ∨ ((True ∨ (p5 → True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48113225244097178381067765298 : (((((p2 → (False ∧ p2)) → False) → (((True ∧ (p3 → True)) → ((((True ∨ p5) ∧ p4) ∨ p2) → (p1 ∨ True))) ∨ p1)) → (p2 → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610476478783521036853466918415 : ((((((p5 ∧ (((((((p5 ∧ p2) → p3) ∧ p2) ∧ False) → (p5 ∧ (True → p3))) → (False ∨ (False ∨ False))) ∧ True)) → p4) → p4) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_134263399598898930133377629703 : (((((p3 ∨ p1) → False) → ((p5 ∧ (False → p1)) ∨ (p4 ∨ (p1 → (p1 → (((True → p2) ∧ p2) → p4)))))) ∨ p3) ∨ ((p1 ∧ p2) → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (p3 ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655022481034165251966764562155 : ((((((p2 ∨ p5) → (((((p1 ∨ (False → (p5 ∨ p4))) ∨ p1) ∨ ((p4 ∨ (p4 ∧ p3)) ∧ p2)) ∧ p5) → p5)) → p3) ∨ (p1 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347608969462302809925188563046 : (p3 → (((True → p2) ∧ (p4 → p4)) ∨ (((p5 ∨ (((p1 ∧ p5) ∧ (p4 ∧ (p2 ∨ (p2 ∨ (p3 → p5))))) → False)) → p1) ∨ (False → False)))) := by
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
theorem thm_5_vars_352836448415999078916066845338 : (p4 → ((p2 → p1) → (((((p3 ∨ p2) ∨ ((p1 ∨ p2) ∧ (((p5 → (p2 ∧ p4)) ∧ (p2 → False)) ∨ p2))) ∧ (p1 → False)) ∨ False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42373369084675378860570932430 : (((p4 ∧ (((((p2 → False) ∨ p1) → False) ∧ ((p3 ∧ (((True ∨ p3) ∧ p3) ∨ (p2 → True))) ∨ ((p5 → False) ∧ p2))) ∨ p5)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138162040494692785522523190143 : ((p1 → ((((((p5 → False) ∨ p5) ∧ True) ∧ (p1 → p3)) → (p5 → ((p2 → (False ∨ p4)) ∨ p3))) → (p4 ∧ p2))) ∨ ((p4 ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53014844819269277794888061877 : ((((True ∨ (p2 ∨ (p4 ∨ (p5 ∧ p3)))) → ((True → p5) → p4)) ∧ ((p4 ∧ ((p1 ∨ (p5 ∨ (True → p2))) → p4)) ∧ (p3 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232839711825227506220508835209 : ((p2 ∧ (p5 ∨ p1)) → (p3 ∨ (p5 ∨ (((((p4 ∧ p4) ∨ p1) ∧ p4) ∨ ((((p1 → p3) → p2) → p1) → p4)) ∨ (p1 ∧ (p2 ∨ p3)))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57451293557080059748651507514 : (((p5 ∨ (p3 ∧ True)) ∨ (p4 ∨ ((True ∧ p3) → (False ∨ ((p5 ∨ p3) ∧ ((((p3 ∧ p4) ∨ p4) → p3) ∧ ((True ∧ p4) → p3))))))) ∨ False) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38169997111683127429709892082 : (((((p1 → ((p4 ∧ ((p3 ∧ p2) ∨ p4)) ∧ False)) → (((p3 → False) ∧ p5) ∧ (p1 → (True → p4)))) ∨ ((p4 → p4) → p5)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229751257777169125750340098620 : ((p4 → (p2 ∨ False)) ∨ ((p3 → (((p5 ∨ p5) ∧ (p2 → (((p2 ∧ (p5 → False)) ∨ p5) ∧ p3))) ∨ (p3 → ((p5 → p3) → p3)))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805891978603677015263495397542 : (((p4 → (((((p5 → (p1 ∨ (p3 ∨ (p1 ∨ (((p3 ∨ p1) → p1) ∧ p5))))) → (p3 → ((p4 → p3) → False))) ∨ p5) ∨ p4) ∧ True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757339255517734629728813586671 : (((p1 ∧ ((p3 → p5) ∨ (((((True ∨ ((((True → p3) ∨ p2) → p1) → p4)) ∧ True) ∨ (True → True)) ∧ p5) → (p5 ∧ (p2 → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749025857881090615179758636120 : ((((p4 → p5) → (((p5 ∧ (((p4 ∧ p3) → (p1 ∨ p3)) → p1)) ∧ (False ∨ (p4 ∨ p1))) ∧ ((p5 → ((p4 ∨ False) ∨ p4)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161490944858151187503599941205 : ((p4 ∧ ((p3 ∨ (True ∧ (((p4 ∧ (p3 ∨ (p1 → False))) ∧ (True ∧ p3)) ∨ (p5 → False)))) ∧ p2)) → (((False ∧ p1) ∧ p4) ∨ (p4 → p2))) := by
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
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h13.left
        let h18 := h13.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h13.left
        let h22 := h13.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h23
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h25
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199754312526568997299248151594 : (((True → ((True ∧ (False → False)) ∨ p1)) → False) → (((((p3 → p2) → p1) ∨ p2) → ((p3 ∨ True) → (p3 ∧ ((p3 ∨ p3) ∨ p4)))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → ((True ∧ (False → False)) ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1538510255071705077731418766 : (((p3 ∨ True) → (True → (((False ∨ (((p3 → False) ∨ p4) ∨ ((p1 ∨ ((p3 ∨ p1) → p1)) ∨ False))) → p3) ∧ p3))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111418696755992741701248339488 : (((p3 ∨ ((p4 ∧ (p1 ∨ (True ∧ p3))) → (((p5 ∧ (p5 ∨ (True ∧ (p5 → (p1 ∨ p4))))) → p3) → (True ∧ p3)))) ∧ p5) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324740679530742650325551634065 : (p5 ∨ ((p4 ∧ (False → p2)) → (((False ∧ p3) ∨ (((p4 ∨ (p3 → ((p5 ∨ (p1 → p5)) → p5))) → p5) ∨ p3)) ∨ ((p5 ∧ False) → True)))) := by
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
theorem thm_5_vars_54008122730206345949345947028 : (((((p1 ∧ (p4 ∧ (p1 ∧ p5))) → (p2 ∨ p5)) → p4) → ((((p3 ∨ True) → p4) → (p3 → ((True → True) ∧ (p3 → p5)))) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303042422589167490773627722656 : (False ∨ (p2 → ((((True ∨ (False → ((p3 ∨ (False ∨ ((p4 ∧ ((p5 ∧ True) → p1)) ∨ p4))) ∨ ((p5 ∨ p4) ∧ p4)))) → p5) ∨ True) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232262209251456359282198480143 : (((p2 → False) → p3) → (p3 → (((p1 ∧ p3) → p1) → (((((p2 ∧ ((False ∨ p1) ∧ ((p3 → p3) ∧ p5))) → p1) ∨ p2) → False) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (((p2 ∧ ((False ∨ p1) ∧ ((p3 → p3) ∧ p5))) → p1) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h10.left
      let h14 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h12
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h15 := h4 h5
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166066336156709281290385362953 : (((p5 ∧ True) → (True → ((((True ∧ p3) ∧ p1) ∨ p2) ∧ ((p3 → p5) → (p1 ∧ False))))) ∨ ((False ∧ False) → ((False ∧ p1) → (p4 → p5)))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218336601226902386166366500527 : (((p1 → True) ∨ (p2 ∨ p1)) → ((((p3 ∧ p4) ∨ (((True ∨ p4) ∧ ((p4 → p1) ∧ p4)) ∨ p5)) → False) ∨ (p2 ∨ (False ∨ (p3 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136202945665160838034432943970 : (((False ∨ (((False ∧ p2) → True) ∧ p5)) ∧ (False ∧ ((True ∨ (p1 ∧ True)) ∧ (False ∨ (p1 → ((p3 → True) → p1)))))) ∨ (p1 ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_844965552412824361292913305600 : (((((((True ∨ p3) ∧ True) ∨ False) → (True → ((False → True) → ((p2 → (((p2 ∧ ((False → True) → False)) ∨ p5) ∨ True)) ∧ p3)))) ∨ False) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (((True ∨ p3) ∧ True) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (False → True) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h7
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58008424095050193187834124168 : (((True ∧ False) ∧ ((p3 → (True ∨ (((p3 ∨ (p1 → (p1 → False))) ∧ p4) ∧ (p2 ∧ False)))) → (False ∨ ((p5 ∨ p2) ∧ (False → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148946194254919241649029359766 : (((p2 → (False ∧ (p1 ∨ p5))) → ((p3 ∧ (p5 ∨ ((p5 → p3) → (False ∧ p5)))) ∧ ((p1 ∨ p5) ∧ p5))) ∨ (False → ((p5 → True) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776625831965317181766346751400 : (((p1 ∨ ((p4 ∨ ((p5 → p4) → (False ∨ ((True ∨ p1) → (p4 ∧ (False ∨ (((False ∧ (p1 ∨ False)) → (p2 → p5)) ∧ p5))))))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136992035978107988926401455213 : (((p5 ∧ p4) → ((p2 ∨ (False ∨ ((True → (((p4 → p1) ∧ (p2 ∨ (p2 → (p2 → p2)))) ∧ p4)) ∧ False))) ∨ p2)) ∨ ((p5 → p5) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340900947443760316494039328753 : (p2 → (((p2 → ((p4 → False) → ((p2 ∧ ((False → p2) ∨ p4)) ∨ p3))) → ((p2 → (((p5 → p4) ∨ (p4 → p1)) → False)) ∨ True)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252571383091193218676354821734 : ((p5 → p3) ∨ (((p3 ∨ (p3 ∧ p2)) → (((False → ((p5 → p1) → False)) ∨ False) ∧ ((False ∧ True) ∧ (p5 ∨ (p3 ∧ (p3 → p1)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183805694991294283237676995927 : ((((False ∧ (p5 → ((False → p1) ∨ (p4 ∧ p4)))) ∨ p2) ∧ p5) ∨ ((p2 ∧ (p3 → (p4 ∨ True))) ∨ ((False → p3) → (p3 → (True ∨ p4))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40371295414640385517171249605 : (((((p4 ∨ (((p4 ∨ (False → (p2 ∨ p2))) → ((p4 ∧ p5) → ((p5 ∨ (p4 → p4)) ∧ (False → True)))) ∨ True)) → p3) ∨ p4) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177988461692856828237284773349 : (((p4 ∧ (p5 ∧ ((p5 ∨ (p1 ∨ ((p5 ∨ p4) → True))) ∨ p3))) ∨ p4) ∨ (True → (((p1 → p1) ∨ p1) ∧ (p1 ∨ ((False → False) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765484753036894065650742704024 : (((p4 ∧ (((((p5 ∨ ((p1 ∧ (((p4 ∧ p2) ∧ p1) ∨ p3)) ∨ False)) ∧ p5) ∨ True) ∧ True) ∧ (p5 → (True ∧ (p1 → (True ∨ p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184751249980157126444367064300 : ((((p3 ∧ p4) ∨ (p1 → p1)) ∧ ((p1 ∧ p2) ∧ (False ∨ True))) ∨ (p3 ∨ ((True ∨ ((p3 ∧ p5) → p2)) ∧ (((False ∨ p4) ∧ p5) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715334347180539756100046635971 : ((((p4 → (p2 ∧ ((p4 → False) ∧ p1))) → ((p4 ∨ (p2 ∨ (p3 → p2))) ∨ (p2 → (p3 ∧ ((p4 ∨ p1) → (p5 ∨ (True ∧ p4))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304984938152028033195050655342 : (p1 ∨ ((((False ∧ p2) ∧ (p5 ∨ (((((p1 ∨ p2) → ((p4 ∨ p4) ∨ (p3 ∨ p4))) ∧ p3) → p1) → p3))) ∨ True) ∨ ((False ∧ p2) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181016345002204254482055640091 : (((p4 ∨ False) ∨ ((p5 ∨ (((p1 ∧ False) ∧ p1) → p4)) ∧ (p2 ∨ p4))) → ((p3 ∨ p4) ∨ (((p4 ∨ p5) → (p2 ∨ (True ∨ p1))) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h10
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h9
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
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
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h18 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h15
      case inr h19 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805210378699739954686645736465 : (((p3 → (p3 ∧ ((((((True ∨ (p1 ∧ (p3 ∨ p3))) ∨ p1) ∧ (True ∧ p4)) ∨ (p5 ∨ p1)) ∧ p1) → (p5 → ((False ∨ p2) ∨ p3))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h8.left
        let h12 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h8.left
          let h18 := h8.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h8.left
          let h21 := h8.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h8.left
      let h24 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h26 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h27 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801239503867128044159202009010 : (((p2 → ((False ∨ (((((((p2 ∨ (p5 ∨ p5)) ∨ p3) → False) ∧ True) → p2) ∧ p4) → p5)) ∨ (((p4 ∧ p3) ∨ (True → p1)) → True))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134480558555046958103968429263 : ((((((p5 → (((p3 ∧ (((p4 ∨ False) ∧ (p3 → p1)) ∧ p1)) ∧ (False ∨ p1)) ∨ p2)) → False) ∧ p5) ∨ p4) → p4) ∨ (False → (p3 ∧ False))) := by
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
theorem thm_5_vars_191862998813111558795983327699 : ((p4 ∨ ((p5 → (p3 ∨ (False ∨ (False ∧ p5)))) ∨ p4)) ∨ (p5 → (((p4 ∨ p4) ∨ ((p1 → p5) ∨ False)) → (p1 ∨ (p1 → (True ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135881669256023831684283723515 : (((p3 ∧ ((((False → p2) ∨ p3) ∧ ((p1 ∨ False) ∨ p2)) → p5)) ∨ (((False ∨ (False ∧ p1)) → p4) ∨ (False ∧ p5))) ∨ (p1 ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313126641647986405638575265866 : (p3 ∨ (((((True ∨ False) ∧ (False ∧ ((p2 ∨ p5) → True))) ∧ ((((p5 → p1) ∨ p2) ∧ True) → p3)) ∨ (False ∧ ((p4 ∨ p3) ∨ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61306481699595610735114887379 : ((False ∧ (p1 → (p3 ∧ (((p1 → p5) ∧ True) ∧ ((((p4 ∨ p1) ∨ True) ∧ (p5 → (p4 ∨ p3))) ∧ ((p3 ∧ p3) ∧ (p1 ∨ True))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225220388301746264004576633351 : (((p5 ∧ p1) ∧ p1) ∨ (p4 ∨ (((True ∧ ((True ∧ p3) ∧ (True ∨ p1))) ∨ (p5 ∨ ((False ∧ (((p4 ∧ p4) → p4) ∨ p5)) → p1))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_137810125570580558959816997628 : ((p3 ∨ ((((p5 → (((p1 ∧ ((False ∧ p2) ∨ False)) ∧ p5) ∨ p2)) ∧ ((False ∧ p4) → p2)) ∧ (False ∧ p3)) ∧ p3)) ∨ ((True → p2) → p2)) := by
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
theorem thm_5_vars_353350451968780621397559983908 : (p4 → (False ∨ ((((((p5 ∨ p1) ∨ ((True ∧ True) ∨ ((((False ∨ p1) ∨ p3) → True) ∧ p4))) ∧ (p1 → False)) ∨ p1) ∨ (p4 ∨ p4)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111267483463840954965170615229 : ((((p4 → p1) ∨ ((p1 → (((p1 ∨ p2) ∨ (p1 ∨ p2)) ∧ (False ∧ p3))) ∧ (p2 → ((p3 → p4) ∧ (p5 ∧ p2))))) ∧ p5) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635471963254186988562723254472 : (((((p1 → ((((p2 → p4) ∨ ((True ∨ True) ∨ False)) → p4) → (p4 ∨ (p4 ∨ (False ∨ p5))))) ∧ ((p2 → p1) ∨ (p3 → p5))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67910416801705579688552133546 : ((p2 → (((((p1 ∨ ((p4 ∧ (p2 ∧ p4)) → p5)) → True) ∨ p3) ∧ p5) ∧ ((p3 ∨ (((p3 ∧ p3) ∨ p4) ∨ p1)) ∨ (p1 ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114362764184047887523162200638 : ((((p3 ∧ (((p2 ∧ (False ∨ (False ∨ (False ∨ (p3 → (p5 → p2)))))) ∧ p4) ∨ p3)) ∧ p3) ∨ (p3 ∧ ((False → True) ∧ p1))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45848212801467950209890836233 : (((p2 → (True ∨ (p3 ∨ (p4 ∨ ((p5 → True) → ((((False ∨ False) ∨ (True → p3)) ∨ ((True → (p1 → False)) ∧ False)) ∧ True)))))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75899702845147840447450761903 : ((((p3 → (((p1 ∧ (p3 ∧ p2)) ∧ ((((p5 ∨ p3) ∨ p5) ∨ ((True ∧ ((p5 → p4) ∧ p5)) ∧ p4)) → p1)) → p5)) ∨ True) → p5) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 → (((p1 ∧ (p3 ∧ p2)) ∧ ((((p5 ∨ p3) ∨ p5) ∨ ((True ∧ ((p5 → p4) ∧ p5)) ∧ p4)) → p1)) → p5)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670118703359674763260643331083 : ((((((p5 ∧ (p4 ∧ (p1 ∨ p1))) ∨ p3) ∨ (((True ∨ p2) → True) → (((p2 → p5) ∧ (p1 → p3)) → p3))) ∨ ((p1 ∨ p2) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112647331891009062160666550688 : ((((((p2 → (((p4 → ((p3 ∧ (p2 ∧ p1)) ∧ (p4 ∧ p4))) ∨ p5) → p5)) ∨ p5) ∨ p4) ∧ ((p1 ∨ p2) → p4)) → p5) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134600997571885041464405407070 : ((((p2 ∧ (True ∨ (((p3 ∨ (p2 ∨ ((False → (p5 ∧ p4)) ∧ p2))) ∧ p5) ∨ (p5 → False)))) → (p3 → p4)) → p3) ∨ (p4 → (p4 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47858956635579880910297162379 : (((((((True → p4) → (p1 ∧ p5)) ∧ ((True → p3) → (((p5 ∨ (p3 ∨ p2)) ∨ p3) → p5))) ∧ p5) ∧ (p4 → p3)) → (p4 → p3)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h9 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h10 := h4 h9
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159265110232229362165647068492 : ((p4 → ((((p1 ∨ (p5 ∧ ((p4 ∧ p2) ∨ False))) ∧ (p5 ∧ (True → p4))) ∨ (True ∧ p5)) ∧ True)) ∨ (False → ((True → p1) ∨ (p4 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228458736630612237067364715186 : ((False ∨ (p3 ∨ p1)) ∨ ((p3 ∨ (((False → ((p3 → p5) ∨ ((False → (p1 → p4)) ∨ p5))) → (p4 ∧ p4)) → (p5 ∨ (True → p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192233056100069494979199450265 : ((((((p3 → p3) ∨ p3) ∧ p3) ∨ (p2 ∨ True)) ∧ p5) → (((p3 → p1) → (False ∨ ((p5 → p2) ∨ (p2 → (p1 ∧ p2))))) ∨ (False → True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
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
theorem thm_5_vars_55330738678270307497794520942 : (((p4 ∨ ((p4 → True) ∧ (p3 → p5))) ∨ ((p4 ∨ ((p1 ∨ ((p5 → False) ∧ ((True → p1) ∧ ((True ∨ p5) ∧ p2)))) ∨ True)) ∨ p2)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136633854829524472229792834366 : ((((p5 ∨ True) ∨ False) → (True ∧ ((p1 → False) ∨ (((((p3 ∨ p3) ∨ p5) ∧ (p2 → False)) ∨ p1) ∨ (False ∨ p1))))) ∨ (p5 ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323477267996492900395354809698 : (p5 ∨ ((((p3 → p4) ∧ (((False → p5) → ((p3 → p3) ∧ p3)) ∧ (p2 ∧ ((p4 ∨ p1) ∨ (p3 ∧ p2))))) ∨ False) ∨ (True ∨ (p5 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749110334725137509427480004478 : ((((p5 → False) → ((((p2 → p5) → p5) ∨ True) → (p3 → ((((p5 → p3) → p1) ∧ ((p5 → False) → p5)) ∧ (True ∧ (p1 → p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203535608632100731807425705954 : ((False ∨ (False → ((p4 ∧ p1) ∧ False))) ∧ (((((p1 ∨ p1) ∨ p3) → False) ∨ (True ∨ (p4 ∨ p1))) ∨ ((False → (p2 ∨ (False ∨ p2))) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310322251880085045120156728721 : (p2 ∨ (((((p5 → False) ∧ p2) ∨ ((p2 → False) → True)) ∨ p4) → ((p1 ∧ (((True → p1) ∧ p1) ∨ (p2 → (True ∧ (True ∨ False))))) ∨ True))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_770011343719256843399207272708 : (((p5 ∧ (p2 → (((p4 ∧ p1) ∧ (((p4 ∨ (False ∧ p2)) → (p2 ∧ p5)) ∨ (p4 → ((False ∨ True) ∨ p1)))) ∨ (p2 → (p3 → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315027596360204407826421981691 : (p3 ∨ ((p4 ∧ (p2 ∧ ((p5 → (p1 ∧ p3)) ∧ False))) ∨ (p5 → (((False ∨ ((((p1 → (p3 ∧ p5)) → p2) ∨ p5) → p2)) → p4) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165975278237144806297318367901 : (((p4 → p2) ∧ ((True → (p2 ∨ p5)) → (p3 ∧ (((True ∨ p5) ∧ (False → p5)) → p5)))) ∨ (True ∨ ((p1 ∧ (p5 ∧ p3)) → (p5 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227951286266813457643483418918 : ((p3 ∧ (p4 ∧ True)) ∨ (((p3 → p1) → ((((p5 ∧ p4) ∧ p2) ∧ p3) ∨ (p4 → p4))) ∧ ((False → (p5 ∨ False)) ∨ (p5 ∨ (p2 → p1))))) := by
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
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192712654228572525626216777181 : (((((p4 ∧ p1) ∧ p5) ∨ ((False ∨ p2) ∨ True)) → p2) → ((False ∧ (((p2 ∧ ((False ∨ p1) ∧ ((True ∧ p3) → p2))) ∧ False) ∧ p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172733685480817203049222586223 : (((p3 → p1) ∨ (p1 ∨ (p5 ∨ (((p5 ∨ (p3 ∨ p4)) → True) → (False ∧ p1))))) ∨ (True ∨ (((p4 ∧ p4) → (p2 → (p3 → p1))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68602985619158694341390527141 : ((p4 → (((p4 ∧ (((p4 ∧ True) ∧ True) → ((True → (((p3 ∨ p5) → p5) → ((False ∧ False) ∧ p3))) ∧ (p1 ∨ True)))) ∨ False) ∨ p4)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



