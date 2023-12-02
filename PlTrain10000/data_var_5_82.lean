variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317639530723866938545472418994 : (p4 ∨ ((((p4 ∨ False) ∨ (((p3 ∨ p5) → ((p1 ∨ (((((p1 → p1) → p1) → False) → (True ∨ p1)) ∨ p2)) → p1)) ∨ True)) ∨ p4) ∨ p4)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205502793503881965404952781503 : (((p3 ∧ p2) ∧ ((True ∨ p4) ∧ p2)) ∨ (((p4 ∨ (((p3 ∨ False) ∨ (((False ∨ p1) → p2) ∨ ((False → p1) → p5))) ∧ p1)) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191763113138286291115740657322 : ((p1 ∨ ((((p4 → p3) ∨ (p4 → p5)) → p5) ∨ p2)) ∨ (((False ∧ (p1 → ((True → p3) ∨ (p2 → (p5 → p2))))) → p1) ∨ (True ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674669108612049088552270996866 : ((((p1 → (False ∧ ((p4 ∨ ((p3 ∧ p1) → (p2 ∧ (True ∨ (True → (False ∨ p3)))))) → (p1 → (p4 → False))))) → ((True → p4) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114409427113509704094067341316 : ((((False → (p3 → (p3 → p2))) → (p5 ∧ (p5 ∧ ((p4 ∧ ((p2 ∧ p4) ∨ p5)) ∧ p1)))) ∨ ((p1 ∨ p1) ∨ (False → p5))) ∨ (p3 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38204331721855556680459304219 : ((((((p1 ∨ (p4 ∧ True)) ∧ (((p4 ∧ p2) → (p2 ∨ p5)) ∧ (p1 ∨ (p2 → True)))) ∧ (p1 ∨ True)) → ((p1 ∧ True) ∧ p3)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50381092725788161839118299543 : ((((p5 ∨ p2) ∧ (p4 → (p5 ∨ (p4 ∧ (False ∧ (((True ∧ False) → ((p5 ∨ p1) ∧ True)) ∧ p5)))))) ∨ (p5 ∧ ((p3 ∧ True) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663959160828574105103086068430 : ((((p4 ∧ (p2 ∧ ((p3 → p1) → (p3 ∧ (p4 → ((True ∧ ((((False ∨ p4) ∨ p5) → (False ∧ p1)) → False)) ∨ p4)))))) → (p5 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303938989220078961176906352861 : (p1 ∨ ((((((p2 ∨ p3) ∧ p5) → p1) ∧ p5) ∨ (p1 ∧ ((True ∧ (p4 → p2)) ∨ ((p5 → p2) → (p4 → ((p3 ∧ p4) ∧ p4)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193758606953651928106607666359 : ((p3 ∧ ((p3 → p3) ∨ (True ∨ ((p4 → False) → p5)))) → (((False ∧ p4) ∨ ((((p1 ∧ p4) → (p3 ∨ False)) → p5) ∨ p3)) ∧ (p3 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308375942285810702485994307076 : (p2 ∨ ((((((p2 ∨ p1) ∧ ((p4 ∨ p3) ∧ p1)) → ((False ∧ p2) → ((p5 ∨ ((p3 ∨ (False ∨ True)) ∧ True)) → p1))) → False) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219438164957559413803691038035 : ((p4 ∨ ((True ∧ p1) → p4)) → ((p3 → ((((((p4 ∧ (p5 ∨ False)) ∨ p2) ∧ False) ∧ p3) ∨ p2) ∨ True)) ∨ (p1 ∨ (p4 → (p3 → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21721698137980102062601545871 : ((((p1 ∧ p2) ∨ ((True ∨ (p4 ∧ (p3 ∨ True))) → p3)) → ((((p2 ∧ p3) ∧ (p2 ∧ p2)) ∨ ((False ∧ False) → (False → p5))) ∨ p2)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306420728667645807680219906750 : (p1 ∨ ((p4 ∧ p1) ∨ (((p3 ∨ (((p4 ∨ p2) ∧ (True → p3)) → False)) ∨ True) ∨ ((True ∧ p2) ∧ (p5 → ((p2 ∨ (p2 ∨ p1)) → p3)))))) := by
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
theorem thm_5_vars_45318385185183363706245636570 : (((p3 ∧ ((((p5 ∨ (p5 ∨ p3)) ∧ ((p5 → (p5 ∧ ((p2 ∧ True) ∨ p5))) ∨ p4)) → (p2 ∨ p2)) ∧ (True → (p3 ∧ False)))) → p5) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54181210333606388549511487500 : ((((p1 ∧ (p3 ∧ ((True ∧ p2) ∨ p4))) ∧ p5) ∧ (((p2 → p3) ∨ (((p4 → p4) → p2) ∧ (p3 → ((True ∨ p2) ∨ p3)))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179220107065395361312536862107 : ((p4 ∧ ((False ∧ (p1 ∨ False)) ∧ (p5 ∨ (p5 ∧ ((p3 → p5) → p2))))) ∨ (((True ∧ p1) ∧ False) → (((True ∨ p5) → False) ∨ (True ∨ False)))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148791962885683886680934821607 : (((p5 ∨ (False ∨ (p3 ∨ (p5 ∨ p1)))) ∨ (p1 → ((True → p2) → ((False ∧ p4) → ((p2 → False) ∨ p3))))) ∨ (p1 ∨ (p3 → (p4 ∨ p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596136666306904033337816039873 : (((((p3 → (p5 → (p2 ∧ (((p4 ∧ p4) → p1) → True)))) → (p5 ∧ ((p2 ∨ ((p5 ∨ p1) ∨ (p1 ∧ (False ∧ p1)))) → p5))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65781166032273734334797123262 : ((p4 ∨ ((p2 ∨ ((p2 ∨ (p5 ∨ (True → (False → (p1 → (p4 ∨ p4)))))) → p4)) ∨ ((((p3 → False) ∧ p1) ∨ p5) ∧ (False ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643505146830653933600319763064 : ((((p4 ∧ ((((p1 → False) ∨ p3) → (p4 ∧ (p5 ∧ (p5 ∧ p5)))) ∨ ((p2 → p2) → ((False → p5) → (p1 ∨ (False ∨ False)))))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308515241811596782478832021398 : (p2 ∨ (((((p3 → p3) → ((((p3 ∧ p5) ∧ p4) ∧ p4) ∨ (False ∨ p5))) ∨ (True ∧ p5)) ∨ (p1 → ((p1 ∨ (False ∧ p3)) → p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159323448782755888051464316907 : ((p5 → (((True → False) ∧ p1) ∨ ((((p2 ∧ True) ∨ (p2 → ((False ∧ p4) ∨ p4))) → False) ∨ p5))) ∨ ((((True → p1) ∧ p4) ∨ True) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806150002916686342277946348262 : (((p4 → (((((((p4 → (((p1 → p5) ∧ False) → True)) ∨ p4) ∧ True) → p5) ∨ (((p1 → p1) → p1) ∨ (p1 ∨ p3))) ∧ p3) ∨ p4)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304013680357024432212301219161 : (p1 ∨ ((True ∧ ((p3 ∧ ((p2 ∨ p2) ∨ ((((p2 → (True ∨ p3)) → False) → p5) ∨ p4))) ∧ ((((p4 → True) ∨ True) ∧ p2) ∨ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133911622054701641134465582325 : (((p3 ∨ ((p4 ∧ ((p3 ∨ ((p2 → ((((p1 ∨ (p3 ∧ True)) → False) ∨ p4) ∧ False)) → p2)) ∧ p2)) ∨ False)) ∧ p2) ∨ ((p3 → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52684083080562878371039955056 : (((p4 ∨ ((p1 ∧ (False → p5)) ∨ ((p2 → (False ∨ p4)) ∧ (False ∨ True)))) ∨ ((True → p4) → (((True ∨ p4) ∧ p1) ∨ (p1 ∨ p4)))) ∨ False) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177999860089890819175175162000 : (((p1 ∨ ((p4 → (p3 ∨ True)) → (p3 ∧ ((p5 ∨ p4) ∧ p5)))) ∨ p4) ∨ (((False ∧ True) ∨ (p2 ∧ (False → (False → (False ∧ p2))))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204327053423103045194346743872 : (((p3 ∧ (False ∨ (p5 ∧ p3))) ∧ p3) ∨ ((False → p5) ∨ (True ∨ (p4 → ((True → (False ∧ True)) → ((p4 → ((p5 ∨ False) ∧ p1)) → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126078292028670508794348054074 : ((True ∧ (((True ∨ p1) → ((p1 → (False ∨ ((False ∨ ((p2 → p1) ∨ True)) ∨ ((p1 ∨ p3) ∧ p4)))) ∧ (p1 ∧ False))) ∧ p1)) → (p3 ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (True ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h11.left
  let h13 := h11.right
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h14 : (True ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h15 := h12 h14
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225071321347590932722290998138 : (((p1 ∧ p2) ∧ p5) ∨ (((((p2 ∨ True) ∨ True) ∧ (((True → p3) → (p5 ∨ p4)) ∧ (p1 ∧ (False ∨ False)))) ∧ (False ∧ p2)) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233743655670498967643118012845 : ((p3 ∨ (p5 ∧ False)) → ((p1 ∧ ((((p2 → ((((True → p2) ∧ True) ∧ False) ∧ p4)) → ((p1 ∧ p1) ∧ p4)) ∧ (p5 ∨ p5)) ∧ True)) ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713961399511221759825818424296 : (((((p1 → ((p1 ∧ p4) → p1)) ∨ p1) → (((True ∧ p5) → (((p3 ∨ (p5 ∨ (p3 ∧ p3))) → True) ∧ p4)) ∨ (False → (p3 ∧ p5)))) ∨ p2) ∧ True) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h5
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180982808706067492133862148383 : (((False ∧ True) ∨ ((((p4 → (False ∧ (p1 ∨ False))) ∧ p4) ∧ p5) ∨ p2)) → ((p3 ∧ (False ∧ (p3 ∨ (((True → p2) ∨ p4) ∧ False)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h11 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h12 := h9 h11
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324415064823089299441127095261 : (p5 ∨ ((p2 ∧ ((False ∧ p3) → (p4 → p2))) → ((((True → ((((p1 ∨ p5) ∧ (p5 ∨ False)) ∧ True) ∧ False)) ∧ (False → False)) ∨ True) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_33344017763979791970650560914 : ((p4 ∨ (((False ∧ ((p2 ∨ (p1 ∧ p3)) ∧ p2)) ∨ ((p4 ∨ True) ∨ ((p1 → ((False → False) ∨ p3)) ∧ (True ∨ p1)))) ∧ (p5 → True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300868744775310405772771980700 : (False ∨ (((True ∧ ((p5 ∨ (p3 ∧ p2)) → (False ∧ (p1 ∨ (p5 ∧ p1))))) ∨ p1) ∨ (((True ∧ (False → (True ∧ (p5 ∨ True)))) ∨ p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88888085323089657194200451867 : (((True ∨ ((True ∨ p4) → False)) → ((((p3 ∨ ((p4 ∧ p3) ∨ ((p2 ∨ ((p5 ∨ p3) ∨ True)) ∨ p2))) → False) ∨ (p1 → p5)) ∧ False)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ ((True ∨ p4) → False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705881845148606105421042816376 : ((((((p2 ∧ p5) ∧ False) ∨ ((p5 → p4) ∨ True)) ∧ ((p3 ∨ p1) ∧ (p2 → (p5 ∧ ((((False ∧ (p1 → p4)) → True) → p2) → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178350244450319895321429238401 : (((p4 ∧ ((True → p4) ∨ (p5 → ((True ∧ p2) ∧ p3)))) ∨ (p2 ∧ False)) ∨ (((p4 ∨ p5) → ((p5 ∧ p3) ∨ (p5 ∧ (p5 ∨ p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168807839509809764622271232326 : ((p2 ∨ ((((p5 ∨ p1) ∧ p2) ∨ (False ∧ (p3 → p5))) ∨ ((p3 → p2) ∨ (p3 ∨ p5)))) → ((p5 ∨ p4) → ((p2 ∧ (p1 ∨ True)) ∨ True))) := by
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
          -- Conjunctions on the left can always be decomposed.
          let h8 := h7.left
          let h9 := h7.right
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h10 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h11 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- False on the left can always be used.
          apply False.elim h13
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h24.left
          let h26 := h24.right
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h27 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h28 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h29 =>
          -- Conjunctions on the left can always be decomposed.
          let h30 := h29.left
          let h31 := h29.right
          -- False on the left can always be used.
          apply False.elim h30
      case inr h32 =>
        -- Disjunctions on the left can always be decomposed.
        cases h32
        case inl h33 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h34 =>
          -- Disjunctions on the left can always be decomposed.
          cases h34
          case inl h35 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h36 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51156393783527511913196138220 : ((((p2 ∨ (((p3 → (((p3 ∧ p2) → (p3 → p2)) ∨ p3)) ∧ p5) ∧ (p3 ∨ p4))) → p2) ∨ (((True ∨ False) ∧ (p5 ∧ False)) → p1)) ∨ p4) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655473126178603408190249566489 : (((((True → (((p1 ∨ (False ∨ p4)) ∧ ((False → (p5 → (p3 ∨ p1))) → (p3 ∨ (p2 ∨ False)))) ∨ True)) ∨ (True → p2)) ∨ (p5 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_383363432042850139838124517763 : (((((p2 → (p4 ∨ (p3 → ((((p5 ∧ p3) ∧ (p1 ∧ False)) ∧ (p1 ∧ ((p2 → p5) ∧ p3))) ∨ (False ∧ (p4 ∧ p4)))))) ∨ True) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_54594270304129678140313549205 : (((True → ((p3 → ((p3 ∨ True) ∧ p3)) → p2)) ∨ ((p4 ∨ ((p4 ∧ ((p4 ∧ (p3 ∧ p2)) ∨ (p3 → p4))) → (p2 ∨ p2))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141283888361428714191245931577 : ((((p3 ∧ p3) ∧ (p1 ∨ True)) ∧ ((p1 ∧ ((((p3 → True) ∨ (False ∨ True)) ∨ p5) ∧ ((p1 ∨ p5) → p3))) ∧ p5)) → (p3 ∧ (p4 ∨ True))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- One of the premise coincides with the conclusion.
          exact h7
    case inr h20 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h3.left
    let h23 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h22.left
    let h25 := h22.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- False on the left can always be used.
          apply False.elim h31
        case inr h32 =>
          -- One of the premise coincides with the conclusion.
          exact h7
    case inr h33 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  -- Conjunctions on the left can always be decomposed.
  let h34 := h1.left
  let h35 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h36 := h34.left
  let h37 := h34.right
  -- Conjunctions on the left can always be decomposed.
  let h38 := h36.left
  let h39 := h36.right
  -- Disjunctions on the left can always be decomposed.
  cases h37
  case inl h40 =>
    -- Conjunctions on the left can always be decomposed.
    let h41 := h35.left
    let h42 := h35.right
    -- Conjunctions on the left can always be decomposed.
    let h43 := h41.left
    let h44 := h41.right
    -- Conjunctions on the left can always be decomposed.
    let h45 := h44.left
    let h46 := h44.right
    -- Disjunctions on the left can always be decomposed.
    cases h45
    case inl h47 =>
      -- Disjunctions on the left can always be decomposed.
      cases h47
      case inl h48 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h49 =>
        -- Disjunctions on the left can always be decomposed.
        cases h49
        case inl h50 =>
          -- False on the left can always be used.
          apply False.elim h50
        case inr h51 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h52 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h53 =>
    -- Conjunctions on the left can always be decomposed.
    let h54 := h35.left
    let h55 := h35.right
    -- Conjunctions on the left can always be decomposed.
    let h56 := h54.left
    let h57 := h54.right
    -- Conjunctions on the left can always be decomposed.
    let h58 := h57.left
    let h59 := h57.right
    -- Disjunctions on the left can always be decomposed.
    cases h58
    case inl h60 =>
      -- Disjunctions on the left can always be decomposed.
      cases h60
      case inl h61 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h62 =>
        -- Disjunctions on the left can always be decomposed.
        cases h62
        case inl h63 =>
          -- False on the left can always be used.
          apply False.elim h63
        case inr h64 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h65 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263080357075028750538193275008 : (True ∧ ((((True ∧ ((((((p5 ∨ True) ∨ (p2 → p3)) → True) ∨ p2) ∨ (p2 ∧ p1)) → p2)) ∨ (False ∧ (p5 → p1))) ∨ True) ∨ (p1 ∧ p1))) := by
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
theorem thm_5_vars_38360159181293819537749839765 : (((((True ∧ ((False → ((True ∧ p2) → ((p4 ∨ (p5 ∨ p5)) ∧ True))) ∧ p3)) → p5) ∨ (p5 ∨ ((p3 ∨ p3) ∧ (True ∨ True)))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173915053936947564928903349133 : ((((p4 ∨ ((p2 ∨ False) → (p5 ∧ (p5 ∧ ((p3 → True) → False))))) → p4) → True) → (((p5 ∨ False) ∨ ((p3 ∨ (True ∧ True)) ∧ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630619712390304407554867665358 : (((((p5 ∨ (p3 ∨ ((p1 ∧ p4) ∨ (((p4 ∧ p4) ∧ p4) ∧ (True → (((True → (True ∧ (p2 ∧ p2))) ∧ p4) ∨ p5)))))) ∨ p1) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338221492722395068684599965020 : (p1 → ((((p2 ∧ (p3 ∨ p2)) ∨ p5) ∧ False) ∨ (True ∨ ((p5 ∨ ((((False ∨ True) → (p1 → p2)) ∨ p4) → (False → (p2 → p1)))) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135030635407469241830038209234 : (((((p3 → (True → (((True → True) ∧ (p5 ∨ ((p4 ∧ (False ∨ p5)) → p1))) → p5))) ∧ p4) ∧ p3) ∨ (p3 → False)) ∨ (True ∨ (True ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115156628657626937620860086233 : (((p2 → (False → (((True → ((p2 → p1) ∧ p2)) → p5) → p2))) → (((((p3 → p3) ∨ p1) → False) → (p4 ∨ p2)) ∧ p5)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136503064729370300215265512072 : (((True ∧ (p3 → True)) ∧ (((p3 → (False → p3)) → p3) ∧ (p3 ∧ (p5 ∧ (((p4 ∨ (p5 → p3)) ∧ p4) ∧ False))))) ∨ (True ∨ (False ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38732037396214832448746106216 : ((((p2 ∧ (p1 → (p5 ∨ (p2 ∨ p4)))) → ((p2 → True) → (((p2 → (True → False)) ∧ (p4 ∧ (p5 → p1))) ∧ (p4 ∨ p3)))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299220994695581553866418805493 : (False ∨ (((p4 → ((((p3 ∧ p2) → p1) ∧ ((p4 ∨ (p4 → (p3 ∧ ((p1 ∧ p4) ∧ False)))) ∨ p3)) ∨ (p3 ∧ p2))) ∨ (p4 → True)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689251194278524740907807703045 : (((((p1 ∨ (p5 → ((False → (p5 ∨ (p1 → ((p2 → p5) → p1)))) ∧ True))) → p4) ∨ (p4 ∨ (True ∧ ((p4 → (False ∨ p2)) → True)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_978111291715771198294379378861 : (((True ∧ (p1 ∧ (p3 ∧ ((p3 → (((p4 ∨ p3) ∨ p1) ∧ ((True → p5) ∧ p4))) ∧ ((((p2 ∨ p5) ∨ p2) ∨ (p2 → False)) ∨ p4))))) → p4) ∧ True) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h14 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h6
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h15 := h8 h14
          -- We need to get the right conjuct of h15 based on <expert-advice>.
          let h16 := h15.right
          -- We need to get the right conjuct of h16 based on <expert-advice>.
          let h17 := h16.right
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h18 =>
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h19 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h6
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h20 := h8 h19
          -- We need to get the right conjuct of h20 based on <expert-advice>.
          let h21 := h20.right
          -- We need to get the right conjuct of h21 based on <expert-advice>.
          let h22 := h21.right
          -- One of the premise coincides with the conclusion.
          exact h22
      case inr h23 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h24 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h25 := h8 h24
        -- We need to get the right conjuct of h25 based on <expert-advice>.
        let h26 := h25.right
        -- We need to get the right conjuct of h26 based on <expert-advice>.
        let h27 := h26.right
        -- One of the premise coincides with the conclusion.
        exact h27
    case inr h28 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h29 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h30 := h8 h29
      -- We need to get the right conjuct of h30 based on <expert-advice>.
      let h31 := h30.right
      -- We need to get the right conjuct of h31 based on <expert-advice>.
      let h32 := h31.right
      -- One of the premise coincides with the conclusion.
      exact h32
  case inr h33 =>
    -- One of the premise coincides with the conclusion.
    exact h33
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170979837220166010444019312162 : ((p2 ∨ ((p2 → (p2 ∧ True)) ∨ (((((p2 → True) → p2) ∨ True) → p1) → p2))) ∧ ((p5 ∧ (((p2 → (False ∨ False)) ∨ p1) → False)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789028263357730052236021153348 : (((p5 ∨ (((p3 ∨ (((p4 ∨ (False → True)) ∨ p4) ∨ p1)) ∧ ((p1 → (True ∨ (False → True))) ∧ ((False → False) ∧ p3))) → (False ∨ p3))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h3.left
          let h14 := h3.right
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h3.left
          let h19 := h3.right
          -- Conjunctions on the left can always be decomposed.
          let h20 := h19.left
          let h21 := h19.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h21
      case inr h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h3.left
        let h24 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h26
    case inr h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h3.left
      let h29 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h31
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805927106858688731482745607127 : (((p4 → (((((p3 → (((False ∨ p5) ∧ False) ∨ p1)) → p2) ∧ ((p5 ∧ (p4 ∨ (p1 ∧ (p1 ∨ (False ∨ True))))) ∨ p2)) → p3) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48427560772788732820542297593 : (((p3 → ((p1 ∧ p1) → (True ∨ ((((p3 ∧ True) ∨ p5) ∧ (p4 ∨ (((p5 ∧ p2) ∨ p2) ∧ False))) ∨ (p2 ∧ p3))))) → (p5 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49070797016171974748771516774 : ((((p1 → (((p3 ∧ (p5 → p4)) → (((p3 ∧ False) → p2) → ((p5 ∧ True) ∧ p2))) → p3)) ∨ (p3 → p4)) ∨ ((True ∧ p1) → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59313800048117180779884609358 : (((p4 ∨ p1) ∨ ((p5 ∨ (p5 → p2)) ∧ (p1 ∧ (p4 → ((((True → (p1 ∨ p4)) ∧ p1) ∧ p1) → (p5 ∨ (True ∧ (False → True)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303976489334466407034785145286 : (p1 ∨ (((p2 ∨ (True ∧ True)) → (p1 ∨ ((p1 ∨ ((False ∨ False) ∨ (p3 ∨ (((p2 → p1) ∧ (False ∨ p5)) → (p4 → p1))))) ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94770227614914445314618264239 : ((p3 ∧ ((((p4 ∨ p5) ∨ ((p2 ∨ p1) ∧ p5)) ∨ p3) → (((((((p5 → p5) → (False ∧ True)) ∧ p5) → p5) ∧ p5) → True) ∧ False))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p4 ∨ p5) ∨ ((p2 ∨ p1) ∧ p5)) ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602851670802374585890298566181 : ((((p1 ∨ (((p1 ∧ True) ∨ ((p2 ∨ ((p1 → ((p2 ∧ (False → p1)) ∧ p1)) ∧ (p2 ∨ (p2 ∧ (False ∨ False))))) ∨ False)) ∨ True)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44771215729673284945306533754 : (((((True → p2) → (p3 ∧ p4)) → (p3 → ((((True → (True ∨ True)) → ((True ∨ p2) ∧ p2)) → p1) ∨ ((p4 ∧ p1) ∧ p1)))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670942695831553331709087447792 : ((((p4 ∧ (((p1 → p2) ∧ p2) ∧ ((p3 → ((True ∨ (True → p4)) ∧ ((p3 ∨ p3) ∨ p5))) → (False ∨ p3)))) ∨ (False → (p1 ∧ True))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773509425132396776064644304111 : (((False ∨ ((((((((p1 ∨ (((p3 ∧ True) ∧ True) ∧ p4)) ∧ True) ∨ p5) → p4) → p2) ∨ (p4 → True)) ∨ ((True ∨ True) → p1)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764286149391002177132989960654 : (((p4 ∧ (((p1 → ((((False → (p2 → p1)) ∧ p5) ∨ p1) ∧ ((p3 ∧ (p5 ∧ (p3 ∨ (p5 ∨ p4)))) ∨ p3))) ∧ (p3 ∧ p3)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60182293410614301930452896363 : (((p5 ∨ p2) → ((((p4 → p1) → p3) → (p3 ∨ ((((p2 ∨ p1) → ((((False ∧ p2) → True) → p3) → p2)) ∨ p4) ∨ p4))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619719126745797198410030456919 : (((((p5 ∧ p5) ∧ (p4 → ((p4 ∧ True) → ((p3 → ((p3 ∨ (p5 → (False ∧ (p5 ∨ p3)))) → (p5 ∧ (p1 → p2)))) ∧ p3)))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57185580722119744139469381423 : ((((p1 ∨ False) ∨ p4) ∨ (p2 ∨ (p4 → ((False ∧ True) ∨ (p3 ∨ ((((((True → p5) ∨ True) ∧ p2) ∨ p1) ∧ (True ∧ p2)) ∨ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604894571666886813441909575040 : ((((p1 → ((False ∧ (p2 → (p5 ∨ p4))) ∧ ((((((True ∧ (p5 ∨ p1)) ∧ (p4 ∨ p5)) → True) ∨ p3) → (p3 → p2)) ∨ p2))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48287599918048581727586862339 : (((p4 ∧ (p5 → (((p4 ∨ p3) ∨ p3) ∧ (((((p2 → (p3 ∧ p4)) ∧ p4) ∧ (p2 → p4)) ∨ (p4 → p3)) ∨ p4)))) → (p1 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118727617655948399099110675807 : ((p5 ∨ ((((((p3 ∧ (p1 ∧ p5)) → (True → (p2 → p4))) ∧ (p3 ∨ False)) → p5) ∨ p1) ∨ ((False → (p4 ∨ p1)) ∨ p3))) ∨ (p4 ∨ p2)) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265530121408396874746968758922 : (True ∧ (False ∨ (((((p5 ∧ p1) ∧ (True ∨ p4)) ∨ ((p3 ∨ ((p4 ∨ p4) ∨ p2)) ∨ (True ∨ p4))) ∧ True) ∨ (p4 → ((p5 → False) ∨ p1))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113129615654976982180588899752 : (((p1 → (True ∨ (True → ((p4 ∨ ((p1 → False) ∨ (True ∨ False))) ∧ (((False → False) → (p4 → (p1 ∧ p5))) → p4))))) → False) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178091771808600669671339839613 : ((((p3 ∧ ((p3 → ((False ∨ True) ∧ (p3 ∨ False))) ∧ p2)) → True) → p1) ∨ ((True → ((p2 → (p5 ∨ p4)) ∧ False)) → (p1 → (p1 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327801375874967510298172899887 : (True → (((((p2 → (p5 ∧ (p3 ∨ p3))) ∧ (p3 ∨ (((False ∨ p2) ∧ ((p5 ∧ (True → False)) → p4)) ∧ p1))) → False) ∨ p4) ∨ (True ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117642084351193126254025263713 : ((p3 ∧ (((((False ∨ ((p4 → (((False ∧ p2) ∧ (False ∧ False)) ∨ False)) → p4)) ∨ False) → p1) → ((p3 ∧ p1) ∨ p5)) → p1)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56527970003141071887127909163 : (((True ∨ (p2 ∧ (p1 → False))) → ((((p4 → p2) ∨ p1) ∨ p1) ∨ ((((p3 ∨ p1) ∨ False) ∨ (((p3 ∨ p2) ∨ p4) ∧ p1)) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55811149467777812839374329959 : ((((p5 ∧ True) → (p2 → p3)) ∧ (((p2 ∨ p2) ∧ (((p5 ∧ p2) ∧ ((p4 → ((p1 ∧ p4) ∨ p5)) → p3)) → (p3 → False))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711251671190490214447024672429 : ((((p5 ∧ (((p4 ∧ True) → p4) ∨ True)) ∧ ((((p5 → p4) ∧ ((p3 → p4) ∨ (((p4 → False) ∨ p5) ∨ p4))) ∧ (p1 ∨ p5)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745338379302625756918343574788 : ((((p5 ∧ p2) → (p1 ∧ (p1 → ((p4 ∨ ((False ∨ (p1 ∨ p1)) → ((((p2 ∨ True) ∨ True) ∧ ((True → p4) ∧ p2)) → p1))) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185626038070001744550621493513 : ((True → ((p5 → p3) → (p4 ∧ (p1 → ((True ∧ True) → p5))))) ∨ (((p3 → p5) → (False → False)) → ((False → p3) ∨ (False → (p3 ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185879032857141611809243138871 : ((((p3 ∨ ((p2 ∨ (p5 → (p4 ∧ True))) → p3)) → p3) ∧ p5) → ((((p4 ∨ (p1 ∨ p4)) → False) ∨ ((False ∧ p4) ∧ (False ∨ p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134261962147019422928819792457 : (((((True ∨ False) ∨ p2) → (((p4 → ((False ∨ (((p1 ∨ p5) ∧ (True ∧ p3)) → p1)) → p5)) ∧ p4) → p3)) ∨ True) ∨ ((p5 ∧ p4) → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197110763376719693162851774364 : (((False ∨ ((False ∨ (p3 ∧ False)) ∧ p2)) ∨ True) ∨ ((False → p1) ∨ (((((p3 ∧ True) → p4) → True) ∧ ((p3 ∧ p2) ∧ (False ∧ p2))) ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607710661344951283610947451947 : (((((False ∨ (((((p4 ∨ p2) → True) → ((((True → p2) ∨ p1) ∨ True) ∧ p2)) ∧ (((p1 ∨ True) → False) ∧ p1)) ∧ False)) ∧ p1) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_612818796083582923083817791321 : ((((((p5 ∧ p2) → ((False ∨ (((p3 → (p5 ∨ (p5 ∧ ((p4 ∨ True) ∨ p3)))) → (p1 ∧ p3)) ∧ p3)) ∧ True)) ∨ (p4 ∨ p5)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_319156676396648073132059301084 : (p4 ∨ (((False ∨ ((p2 ∨ (p2 ∨ p2)) ∧ (p2 → ((p4 ∨ p5) → (p4 ∧ (p2 → p3)))))) ∧ p3) ∨ (p5 ∨ (((p1 → p2) → True) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_46679695499406065512071560509 : (((p2 ∨ ((((p1 → ((p3 ∨ p2) ∨ (((p3 ∨ (p5 → True)) ∧ True) ∧ (p2 ∧ (False ∨ True))))) ∧ p4) ∨ p3) ∨ True)) ∧ (p3 → True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135373829789603585773944926539 : ((((((p1 ∧ ((p4 ∧ (True ∨ (p5 → (True → p1)))) ∨ (p5 → p4))) ∧ p1) ∨ False) ∨ p3) ∨ (p2 ∨ (p2 ∨ True))) ∨ ((p3 → p5) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307776991598545779651709961422 : (p1 ∨ (p3 → (p1 → ((((p3 ∧ (((p3 ∧ (False → (p2 ∧ p2))) ∧ p2) → False)) ∨ True) ∨ p3) → (p4 ∨ (p3 → ((p3 → p4) ∨ p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135374118488011640321290635331 : ((((((p3 ∨ ((p4 ∧ (False ∧ p1)) ∨ p4)) ∨ ((p2 → True) ∨ (False ∨ p1))) ∨ True) ∨ True) ∨ ((p1 → p5) ∧ False)) ∨ ((p2 → p3) → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249125866019282332308104780885 : ((p4 ∨ p2) ∨ (((p1 ∨ (p1 → False)) ∨ (((((((p1 → p4) ∧ p1) ∨ p2) ∧ p5) ∧ p1) ∨ p5) ∨ True)) ∨ (((p3 ∧ p1) → p1) → p1))) := by
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
theorem thm_5_vars_780710417481148291348329931176 : (((p2 ∨ ((((True → True) ∨ p4) → (False ∧ p3)) ∧ (p1 ∧ ((False ∨ (p1 ∧ p4)) ∧ (((False ∧ p3) ∨ (p2 ∧ (p4 → p3))) ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53851283960491134297584592349 : (((((p2 → False) → p3) ∧ (((True ∨ p1) → False) → False)) ∨ ((((((((p1 → True) ∧ p2) ∧ p4) ∧ False) ∨ p2) ∧ p5) ∨ False) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



