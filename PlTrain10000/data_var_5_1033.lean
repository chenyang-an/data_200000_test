variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207269407593981418287229691287 : (((((p3 → p2) ∧ p3) → False) ∨ p4) → (True → (((p2 ∧ False) ∧ (((p2 → (False ∨ p4)) ∨ p3) ∨ (p2 → p3))) ∨ (p3 → (p4 ∨ True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184937834107072261277798357663 : (((p3 → (p1 ∨ p5)) ∨ (p4 ∧ ((p2 → False) ∧ (p1 ∧ p3)))) ∨ ((p5 → ((True ∨ (True → ((True ∨ (True ∧ True)) ∧ p3))) ∧ True)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219822172674491989133529885289 : ((p3 → ((p3 → True) ∧ p3)) → ((((p1 ∨ p4) ∧ (p4 → ((p3 → p2) ∧ True))) → (p1 → (p3 ∨ ((p2 → (p3 → False)) ∨ p1)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602823552095624723445680710654 : ((((p1 ∨ ((((p3 ∨ p1) ∨ (p2 ∧ p4)) ∨ ((p1 → p5) → ((((p2 ∨ True) ∨ (True ∧ p4)) ∧ (p3 ∧ p1)) → p2))) ∧ True)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306011406898667719497718048835 : (p1 ∨ ((p2 ∧ ((False ∧ False) ∧ p2)) ∨ (p3 → (False → ((((True ∧ p4) ∧ (False ∧ p1)) ∧ ((p5 → (p4 ∨ (True ∧ p3))) ∨ p4)) → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h7.left
  let h11 := h7.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125603485145930984505113158558 : (((p5 → p3) ∧ ((p5 ∨ ((False ∧ ((p2 → (((p5 ∧ False) → (True → True)) → (True ∧ True))) → p3)) → p1)) ∨ (p2 → True))) → (p5 → p3)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h7 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h8 := h3 h7
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h10 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h11 := h3 h10
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h13
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137459497325623547561518637503 : ((p4 ∧ (True ∧ (((p2 ∧ p3) ∧ True) → (p3 ∧ (False ∧ (p4 ∨ (p4 ∧ (p3 ∨ (((p1 ∨ False) ∧ p5) ∨ p2))))))))) ∨ (p2 ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208224407200428613991332986217 : (((True ∧ p1) ∧ ((p5 → p3) ∨ p3)) → (((((p2 ∧ (p4 ∧ (((p1 ∨ p2) ∧ False) ∧ (False ∧ p4)))) ∨ p4) → p2) ∨ (p5 → True)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116267230246144001781609515690 : (((p3 ∧ (p5 ∨ p3)) ∨ ((True ∨ p1) ∧ ((p1 ∧ p3) ∨ (p2 → ((((p2 → True) ∧ p4) ∧ False) → ((p3 ∧ True) → p2)))))) ∨ (p2 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695037979727813621735195164483 : (((((p2 ∧ (((p3 ∧ (True → (p2 → (p2 ∨ p2)))) ∧ p2) → p4)) ∧ True) → (((False ∨ p1) ∧ ((p4 ∧ (p3 ∨ True)) ∨ False)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314548168428469597785584475089 : (p3 ∨ ((((p3 ∨ (p1 ∨ ((p3 ∧ p1) → p1))) → p3) ∧ (True → ((True → (p4 ∨ p2)) ∧ p4))) ∨ (p2 ∨ (((p4 → p1) ∨ False) ∨ True)))) := by
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
theorem thm_5_vars_577590203207618537395472330723 : (((p3 → ((((True ∨ p3) ∧ (((p5 ∨ ((p1 ∨ p1) ∨ p1)) ∧ p1) ∨ p4)) ∨ (p3 ∨ (p4 ∧ p2))) ∨ (p2 → ((False ∧ p5) ∧ p2)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678298052007669412778385066994 : (((((True → (((True → p4) ∨ (p4 ∧ p5)) ∧ p3)) ∨ (((True ∧ (p3 ∨ (p2 → True))) → p1) ∧ p2)) ∨ (((False ∨ p5) ∨ p5) → True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617046196689719973599104635653 : ((((((False → (True ∧ True)) ∧ (p5 ∨ (True ∧ p4))) ∧ (((p2 ∨ (((p4 → (p3 ∨ (p1 → p1))) → False) → p1)) ∨ False) → p4)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67898596551937287752576438135 : ((p2 → (((p3 → (False → ((p5 ∧ p5) → ((p2 → p4) ∧ (p5 ∧ False))))) → (p1 ∨ p4)) → (True → ((p2 → (True ∨ p3)) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85916080046581960451420248877 : ((((p2 → ((p5 ∧ (True ∨ True)) ∧ (True ∧ p4))) ∧ p4) ∧ (((p5 ∨ p4) ∨ (((p5 ∨ p2) → (True → p3)) ∧ p5)) → (p2 ∨ p2))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : ((p5 ∨ p4) ∨ (((p5 ∨ p2) → (True → p3)) ∧ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52582568112535605605942528229 : (((((p5 ∧ (p5 ∧ (True ∨ (p4 ∨ p2)))) ∨ p2) ∧ (p1 ∧ (p1 ∨ p3))) ∨ (((True → (False ∨ p3)) ∨ (p2 ∨ p4)) ∧ (False → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_975972762491904839482268306761 : (((True ∧ (((p3 ∨ (p4 ∨ (((((p2 ∨ p3) → (p2 ∨ False)) ∨ True) ∧ (True → True)) ∨ p3))) → ((p2 ∧ p5) ∧ (p1 → p1))) ∧ True)) → p2) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p3 ∨ (p4 ∨ (((((p2 ∨ p3) → (p2 ∨ False)) ∨ True) ∧ (True → True)) ∨ p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- One of the premise coincides with the conclusion.
  exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113361428333202104525966591668 : (((p5 ∧ ((p4 → (((((p4 ∧ (p4 → p4)) ∧ (p3 → p3)) ∨ (p3 ∧ True)) ∧ p5) ∨ p3)) ∨ (False ∧ False))) ∧ (False ∧ p5)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_399453605389571236788660440799 : ((((p2 → (((((p3 → p1) → (True → p5)) → p5) ∧ (True ∨ p4)) → ((p1 ∨ p1) ∨ (True ∨ (p1 → ((False ∨ p4) ∧ True)))))) ∨ p3) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114897162116232931929255453822 : (((True → ((((((p5 ∨ (True ∨ p3)) → p2) ∨ p2) ∧ True) → p4) → p2)) ∨ ((p3 ∨ (p2 ∧ p2)) ∧ (False ∧ (p3 ∧ p3)))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65013309863790239017565800777 : ((p2 ∨ ((False → p4) ∧ ((((True ∧ (True → (p4 → True))) ∧ p5) ∨ p3) ∧ (p2 → ((p3 ∨ (False → (p2 ∧ (p3 ∧ p3)))) → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118384097637798493871813659123 : ((p2 ∨ ((((p1 ∨ (p4 ∧ True)) → False) ∨ ((p4 → p2) ∧ False)) → (((True ∧ (p5 ∧ p4)) → (p5 → p2)) → (False ∧ p5)))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136097633500931888798359957757 : (((((((p3 → p2) → p3) → p3) ∨ False) → p5) ∨ (((p3 ∧ ((p2 → p1) ∧ p3)) ∨ p3) ∧ ((p4 ∨ p3) → p5))) ∨ (p2 → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634733058603479351812653104524 : ((((((((True ∧ p4) → True) → (p3 → (p2 ∧ ((p1 → p2) ∨ (p3 ∧ ((False ∧ True) ∨ p1)))))) → p4) ∨ (p4 ∧ (True ∨ p3))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_476907910518506681407153894969 : ((((p3 ∨ (True → ((False ∧ (p1 ∨ (p1 ∨ p4))) ∨ False))) ∨ (p1 → ((((p5 → p3) ∨ p4) ∧ (p4 ∧ p4)) ∨ ((p4 ∨ False) → p4)))) ∧ True) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61790394046713817570781511963 : ((p2 ∧ ((p4 ∨ (p1 ∨ ((p3 ∧ (((p4 ∨ (p2 ∧ p5)) ∧ p5) → (p3 → p4))) → (p1 ∨ (False ∧ (p3 ∧ (True → True))))))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614122767504281279562169464018 : (((((p3 → (p3 ∧ (((True → (p5 ∨ (True → (p4 ∧ (p2 → p3))))) ∨ p2) ∧ ((False → p5) ∧ p1)))) ∨ ((False ∧ p3) ∧ p3)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_173901338496395583076159537599 : ((((((p1 ∨ (((p4 → p4) ∨ (p5 ∧ p1)) ∧ p3)) ∨ False) → p3) → p2) → p5) → ((p1 ∨ p2) ∨ (((p4 ∧ p5) → p4) → (True ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349994214056779746516895030016 : (p4 → ((((((((False ∧ p1) → False) ∨ p5) ∨ p2) → p3) ∧ (True → (((p1 ∧ (p2 ∧ (p5 ∧ p2))) ∧ (False ∧ p2)) ∨ p3))) ∨ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213158233692262963777443523198 : ((((p2 ∧ p3) ∨ p3) ∧ p1) ∨ ((p4 ∧ ((p3 ∧ p3) → (p3 ∧ (((p3 → (p4 → p3)) → p3) → p2)))) → (p5 ∨ ((p5 → p1) → p4)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121772998863517203946123930645 : (((((False ∧ p4) → False) ∧ (p1 → (((p2 ∨ p1) → (True ∧ (((False ∨ p5) ∧ (False ∨ (p1 ∨ p5))) ∧ p1))) ∨ p1))) → False) → (p1 ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False ∧ p4) → False) ∧ (p1 → (((p2 ∨ p1) → (True ∧ (((False ∨ p5) ∧ (False ∨ (p1 ∨ p5))) ∧ p1))) ∨ p1))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (((False ∧ p4) → False) ∧ (p1 → (((p2 ∨ p1) → (True ∧ (((False ∨ p5) ∧ (False ∨ (p1 ∨ p5))) ∧ p1))) ∨ p1))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
    -- Implications on the right can always be decomposed.
    intro h12
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h8
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320353860207954097094477726616 : (p4 ∨ ((p1 → p4) ∨ (((p5 ∧ p2) ∨ ((((p4 ∨ p1) ∨ True) ∨ p5) → (((False ∧ p4) → False) → ((p4 ∧ True) → (p1 → False))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606781325067198168640956779555 : (((((((((p1 ∧ (p3 ∧ (p2 → p3))) → p1) ∧ (True ∧ p3)) → ((((False ∧ p2) ∨ True) → p5) → True)) → (p1 ∧ p4)) ∧ p2) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_179853067418017712404788151508 : (((p4 ∨ (p4 → (p3 ∨ ((p1 ∧ (p3 ∨ p1)) ∧ (p4 ∨ p3))))) ∧ p3) → ((p2 ∧ (p5 ∨ (p2 ∧ p4))) ∨ (p1 → (False ∨ (p3 → p3))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143844214029667542778793074498 : ((((False ∨ ((False ∨ ((p2 → ((p3 ∨ ((True → p3) ∨ p3)) ∧ p2)) ∨ p5)) → (p1 ∧ p5))) → p5) ∨ True) ∧ (True ∨ ((False ∨ p2) → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109174101735212059318788435471 : ((False ∨ ((((True ∧ ((p1 ∨ ((p1 ∧ (p1 ∨ p3)) → p5)) ∨ (p3 ∧ ((p3 → (p2 ∨ p4)) ∧ p1)))) → True) → p3) ∨ True)) ∧ (False → p1)) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319046785354377574171528479374 : (p4 ∨ ((((p5 → p5) → (((p3 → p5) ∧ p3) ∨ p5)) → (p4 → ((p5 ∨ (p3 ∧ (p1 → p5))) ∨ p3))) ∨ (((p4 ∧ False) ∨ p2) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p5 → p5) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149367579225944882891703193265 : (((False → p3) → ((((p3 → ((p3 ∨ False) ∧ p4)) → p4) ∨ p2) ∧ (p5 ∧ (p5 ∧ (False → (True ∨ p4)))))) ∨ ((p5 → (p1 ∨ p5)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118561989529185888543933880726 : ((p4 ∨ (((((p2 → p5) ∨ p4) ∧ (p4 → ((p1 ∨ p5) ∨ (((p3 ∧ True) → ((p3 → p3) → p3)) ∧ p5)))) ∨ p3) ∧ p3)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751445368286469447844749866608 : (((True ∧ ((p5 ∨ p3) → ((p5 → (((p4 ∨ p1) ∧ (p4 ∨ (((False ∨ p5) ∨ (p3 ∨ True)) ∧ True))) → (p4 ∨ (p3 → p3)))) ∨ p1))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- False on the left can always be used.
            apply False.elim h13
          case inr h14 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h7
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h7
          case inr h17 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h7
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h19 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h24 =>
            -- False on the left can always be used.
            apply False.elim h24
          case inr h25 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h26
            -- One of the premise coincides with the conclusion.
            exact h26
        case inr h27 =>
          -- Disjunctions on the left can always be decomposed.
          cases h27
          case inl h28 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h29
            -- One of the premise coincides with the conclusion.
            exact h29
          case inr h30 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h31
            -- One of the premise coincides with the conclusion.
            exact h31
  case inr h32 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h33
    -- Implications on the right can always be decomposed.
    intro h34
    -- Conjunctions on the left can always be decomposed.
    let h35 := h34.left
    let h36 := h34.right
    -- Disjunctions on the left can always be decomposed.
    cases h35
    case inl h37 =>
      -- Disjunctions on the left can always be decomposed.
      cases h36
      case inl h38 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h38
      case inr h39 =>
        -- Conjunctions on the left can always be decomposed.
        let h40 := h39.left
        let h41 := h39.right
        -- Disjunctions on the left can always be decomposed.
        cases h40
        case inl h42 =>
          -- Disjunctions on the left can always be decomposed.
          cases h42
          case inl h43 =>
            -- False on the left can always be used.
            apply False.elim h43
          case inr h44 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h37
        case inr h45 =>
          -- Disjunctions on the left can always be decomposed.
          cases h45
          case inl h46 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h37
          case inr h47 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h37
    case inr h48 =>
      -- Disjunctions on the left can always be decomposed.
      cases h36
      case inl h49 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h49
      case inr h50 =>
        -- Conjunctions on the left can always be decomposed.
        let h51 := h50.left
        let h52 := h50.right
        -- Disjunctions on the left can always be decomposed.
        cases h51
        case inl h53 =>
          -- Disjunctions on the left can always be decomposed.
          cases h53
          case inl h54 =>
            -- False on the left can always be used.
            apply False.elim h54
          case inr h55 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h56
            -- One of the premise coincides with the conclusion.
            exact h56
        case inr h57 =>
          -- Disjunctions on the left can always be decomposed.
          cases h57
          case inl h58 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h59
            -- One of the premise coincides with the conclusion.
            exact h59
          case inr h60 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h61
            -- One of the premise coincides with the conclusion.
            exact h61
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40829222312881619883979876205 : ((((False → (True ∨ ((True ∨ ((p2 → p1) ∨ (((True ∧ (((p4 ∧ True) ∨ p2) → p5)) ∧ (p1 ∧ True)) ∨ True))) ∨ p3))) → p4) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118759108752486606139895180455 : ((p5 ∨ ((p4 ∨ p4) ∨ (((((False ∨ ((p1 ∧ p1) ∨ (p2 ∧ (p2 ∧ (p3 ∧ p1))))) → True) ∨ (p5 ∨ False)) → p3) → p4))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190326370703184297458422350599 : ((((p4 → ((p2 → True) → p5)) ∨ (p1 ∧ p4)) ∨ p3) ∨ ((p4 ∧ p3) → ((True → False) → (False ∨ (p3 ∧ ((True → p1) ∨ (p4 ∨ p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40111698725761222812479443890 : (((((p3 ∧ ((p4 → (((p4 ∨ ((((True ∧ p2) → False) ∧ False) ∧ True)) → (p2 → p4)) → p3)) ∨ False)) ∨ (p5 ∧ True)) ∧ p5) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1943623624479186612939781631 : ((((p5 ∧ True) ∨ (p2 → (((p5 ∨ False) ∧ (((True ∨ p3) ∧ (p4 → True)) → p1)) → p3))) ∨ False) ∨ (True ∨ ((p3 ∨ False) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586894294470809052310923583628 : (((((False ∨ (((False ∨ (True → False)) ∨ p3) → ((((True → (False ∧ p5)) ∧ (p1 ∨ True)) ∨ (True → p5)) ∨ (p4 ∧ True)))) ∧ p2) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124461609313521489162760483072 : (((True ∨ ((p3 ∧ (True → (p2 → p4))) ∨ p2)) → ((p5 → False) → ((p5 → ((p3 ∧ p1) ∨ (True ∨ (False → p1)))) → p4))) → (p4 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633542302283370952889213419903 : (((((((((True ∨ (p5 → p2)) ∨ False) ∧ p1) ∨ True) ∧ (True ∨ (p4 ∨ (p3 ∨ (False ∨ (p2 → (p3 ∧ p3))))))) ∨ (p3 ∨ p1)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140601647390944746460707299578 : (((((p4 → p2) ∧ (p1 ∨ (((p1 ∧ p4) ∧ (p5 → False)) ∧ p4))) ∨ (p4 ∧ p1)) → (True ∨ (False ∨ (p4 ∧ p1)))) → ((p2 ∧ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768611035984362370499323533910 : (((p5 ∧ ((((p5 → p1) ∧ ((True ∧ (p1 ∨ p1)) ∨ True)) → (p5 ∨ p1)) ∧ ((((p1 → ((p2 → True) → p4)) → p4) ∨ p4) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52541592358384685057788391651 : ((((((p2 → (p2 ∨ ((p2 ∨ (p2 ∧ p3)) ∨ False))) ∧ p2) ∧ p2) → p1) ∨ (False ∨ (((p4 → p5) → p3) ∧ ((p2 ∨ p4) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68757567890416490535204969933 : ((p4 → ((((p5 ∧ (p2 ∨ (p5 ∨ p1))) ∨ (p4 → (p4 ∨ (p4 ∨ True)))) ∧ p2) → (False ∨ ((((p4 ∧ p2) → p4) ∧ p1) ∨ p2)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2188974470267693496499330448 : ((((((p4 → p2) ∧ p5) → (p3 ∧ False)) ∨ p4) ∨ (True ∨ ((p2 → False) ∧ p1))) ∨ ((p2 ∧ (((p1 ∧ p2) ∨ p4) ∨ p3)) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59098623718831342138285483446 : (((p5 ∧ p5) ∨ ((((((p4 → p5) ∨ (p3 ∨ (((p1 ∨ p5) ∨ p4) → p3))) ∧ (True ∨ p1)) ∨ p2) → (p2 ∧ p5)) → (p1 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149469538002864866537974618616 : ((False ∧ ((p1 ∨ p2) ∨ ((True ∨ p5) ∧ (((p2 ∨ (((p3 ∨ (p1 ∧ True)) ∨ False) → p3)) → p1) ∨ p3)))) ∨ ((False ∧ False) → (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250896645333149037633897041579 : ((p1 → p3) ∨ (((True ∧ p3) → (False ∨ p3)) ∧ (p4 ∨ ((p5 → p4) ∨ (False ∨ (((p5 → (p5 → False)) ∨ (p1 → p1)) ∨ (False ∨ p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192924839960771950096092121343 : ((((((p3 ∨ p4) ∨ True) ∨ p1) → p4) ∨ (p2 ∨ p2)) → (((p1 ∨ False) ∨ ((p2 ∧ p4) → (p4 ∧ (True ∨ False)))) ∧ ((p3 ∧ p1) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h10.left
      let h14 := h10.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- One of the premise coincides with the conclusion.
      exact h18
      -- Conjunctions on the left can always be decomposed.
      let h19 := h16.left
      let h20 := h16.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- Implications on the right can always be decomposed.
  intro h21
  -- Conjunctions on the left can always be decomposed.
  let h22 := h21.left
  let h23 := h21.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h24 =>
    -- One of the premise coincides with the conclusion.
    exact h22
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h26 =>
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h27 =>
      -- One of the premise coincides with the conclusion.
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588202801440225548509489932186 : ((((((((((False → p5) ∨ p5) ∧ p4) → True) ∨ False) ∧ (p4 ∨ (p3 ∨ (((p4 ∨ p3) → p2) ∧ ((False ∨ p4) ∨ p1))))) ∨ p2) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336243307269370721700346607995 : (p1 → (((p4 ∧ (p3 → (True ∧ (p4 ∧ ((((p4 ∨ False) → False) ∧ p4) ∨ ((p2 → False) ∨ p2)))))) ∨ ((p3 ∧ (p4 ∨ p5)) ∧ p3)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788393125124025929525325445081 : (((p5 ∨ ((((False → ((True → p3) → (p5 ∨ True))) ∧ ((False → p2) ∨ ((p5 → (True ∨ p5)) ∧ False))) → ((p2 ∨ p4) ∨ True)) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42352390771244337814631558097 : (((p3 ∧ (((False → False) ∧ p4) ∨ ((p5 ∨ p5) → ((p3 ∨ p2) ∨ ((((((p3 ∧ p1) → p2) ∧ p1) ∧ p1) ∧ True) ∧ p4))))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230531521799711237674843644904 : (((False → False) ∧ p5) → ((p2 → ((p1 ∧ (p3 ∨ p4)) ∨ ((p3 → p3) → False))) ∨ ((p5 ∨ p1) → ((p5 ∨ p5) ∧ (p4 → (True ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h8 =>
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
theorem thm_5_vars_198030184129128304387349672849 : (((True ∧ p2) ∨ (p2 ∧ ((p5 ∨ p5) ∧ False))) ∨ (True ∨ ((((p2 ∨ p5) ∧ p1) → p1) → (p1 ∧ (p1 ∧ (p5 ∧ (True ∨ (p2 ∧ False)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62664781725750000567808887577 : ((p4 ∧ ((((p4 ∧ (p4 ∧ (p2 ∧ (p2 ∨ (p4 → p1))))) ∨ p4) → (((p1 → p2) ∨ p1) → (True → (p3 ∧ (p3 → p3))))) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674604024542018634954606957143 : ((((False → (((p3 ∧ (((True → p1) ∧ p4) ∧ False)) → (((False ∨ p1) ∧ p3) ∨ ((p5 ∧ p5) ∨ p3))) → p1)) → ((p2 ∨ False) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797792294575396862407477377923 : (((p1 → (((False ∨ (((p3 ∧ ((p1 ∧ p4) ∧ p4)) ∨ (p4 → (p2 ∨ (p3 → p3)))) ∧ p3)) ∨ (True ∧ (p5 → p5))) ∧ (True ∨ p1))) ∨ p3) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157465275490011378200625676257 : ((((p4 ∧ (((p3 → p2) ∧ (((p4 → p1) ∨ (p5 → True)) ∧ p3)) ∧ p3)) ∨ p4) ∨ (p4 ∧ False)) ∨ (p4 ∨ ((p3 ∨ (True ∨ False)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_245792895757286609949238679258 : ((p3 ∧ p3) ∨ ((p3 ∧ (p5 → ((p3 → (p1 ∧ False)) → False))) ∨ ((((p2 ∨ ((p5 ∨ p4) ∧ p2)) ∧ ((True ∧ False) ∧ p4)) ∧ p3) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h5.left
      let h16 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h5.left
      let h21 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h20.left
      let h23 := h20.right
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704705046080574171270750468202 : ((((p1 ∧ (False ∨ (p4 ∨ (p2 → (p4 ∨ (False ∨ p2)))))) → ((p2 ∨ ((p4 ∨ ((False ∨ p5) ∨ True)) ∨ (p3 ∨ p2))) ∧ (p4 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113728229155023102586772618862 : (((((((True ∧ p3) ∨ p1) ∨ p4) → (((p4 → p5) ∨ ((p4 ∨ p4) ∧ True)) ∧ p2)) ∨ ((p5 ∧ p1) ∧ p4)) → (p3 ∨ p2)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66470261290461215724455886345 : ((True → ((p4 → (p2 ∨ ((p5 ∨ ((p1 → True) → p2)) → (((p1 → ((p2 ∨ p1) ∨ False)) ∧ p5) ∨ ((p5 ∨ True) ∨ p3))))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774523562515929177231891155195 : (((False ∨ (((False ∨ False) ∧ ((p1 ∨ ((((p1 ∨ p4) → True) ∧ True) ∧ p2)) ∨ p4)) ∨ ((True ∧ ((p5 → (False → p5)) ∧ p1)) ∨ True))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117215396851890234862765955742 : ((True ∧ ((p5 → (p2 ∧ False)) ∧ (p2 → (p2 ∧ ((((True → p3) ∧ ((True ∨ ((False ∧ p3) ∧ p5)) ∨ p1)) ∨ p3) ∨ p1))))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62842479615076868596392207180 : ((p4 ∧ (((p3 ∨ p4) → (p4 → (p1 ∨ p3))) ∨ (p3 ∨ (((p5 ∧ (p1 ∨ (False → True))) → p3) → ((p5 → (p4 ∧ False)) ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115085648231023785739418523941 : (((p1 ∨ (((True → p1) ∨ (p4 ∧ (p3 → (p5 ∧ False)))) → p1)) ∨ (p1 → ((False ∨ (((False ∨ p4) → p4) ∨ p2)) ∨ True))) ∨ (p5 ∨ p5)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780320264501739186627316903401 : (((p2 ∨ (((True ∨ (False ∧ False)) → (p3 ∧ ((p1 ∨ p1) → (((p4 ∨ p3) ∧ (False ∨ p4)) ∨ p3)))) ∨ ((p3 ∧ (p1 ∧ p5)) → p1))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225328266595443872499749250385 : (((p1 ∨ True) ∧ p3) ∨ ((p4 ∨ ((((p4 ∧ (((p3 → True) ∨ True) ∧ (((p4 ∧ p5) ∨ (p5 ∨ p5)) → p3))) → False) ∨ False) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301444725673934709420170275837 : (False ∨ ((p5 ∨ (True → (p4 ∨ p5))) → (True ∧ ((p4 ∨ p2) → (True ∧ (((p2 ∨ (p1 → ((True ∧ (p1 ∧ False)) → p3))) → p4) ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h7 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43456458835822884513834405898 : (((((p4 → p5) ∧ (p2 ∨ ((((False ∨ p5) ∨ p5) ∨ p1) ∨ ((p2 → True) → (p4 ∨ ((p2 → False) → (False ∧ p3))))))) ∨ False) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351774265380783884636900882259 : (p4 → ((True → (((p2 ∨ ((p3 ∨ (p4 → (p5 ∨ p2))) ∨ p5)) ∨ True) → p1)) → (((p1 → False) → (p3 ∧ p1)) ∨ ((p2 ∧ p1) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44440562100653077623601156169 : ((((p4 ∨ ((p5 ∨ (p5 ∧ (p5 ∧ (p2 ∧ (p2 ∨ p2))))) ∧ p5)) ∧ ((p4 ∨ (p3 ∨ False)) ∨ (p5 ∧ (p1 ∧ (p3 → p5))))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354697726891778954430093401830 : (p5 → (((p5 → (((p5 ∨ (False → ((p4 ∨ ((p1 ∨ p1) ∧ p4)) → True))) ∨ p5) → (((p3 ∧ p5) ∧ p4) ∨ p2))) ∨ (p2 ∧ p5)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140172050033624068841207691151 : ((((p4 ∨ ((p1 → (p4 → ((((p1 ∧ p5) ∧ p4) ∧ p5) ∧ True))) ∨ False)) ∨ (True ∨ (p4 ∨ p2))) → (p3 ∨ p5)) → ((p5 ∧ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9760423088956324005668108550 : ((((True ∨ p3) → ((((((p1 ∧ p4) ∧ p3) ∧ p3) ∧ p1) → (p4 → False)) ∨ (p4 ∧ (p4 ∧ (p3 ∧ (p3 → (p3 ∨ True))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181250617763974395986835132157 : ((p3 ∧ (p2 → ((p3 ∨ p4) → ((p2 ∨ (p3 ∨ (p3 → p4))) ∧ p3)))) → (((p1 → (((p1 → p2) ∨ (p4 ∧ False)) ∧ True)) ∧ p2) ∨ True)) := by
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
theorem thm_5_vars_135390100222721052205956415913 : (((((((p1 ∨ p4) ∨ ((True ∨ p1) ∧ (True ∧ (p1 ∧ p5)))) → p4) → p3) ∨ (p1 ∧ False)) ∨ ((p3 ∨ p5) ∧ p1)) ∨ (p4 → (p5 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51320609798212276403311245864 : (((p5 ∨ (p1 → ((p1 ∧ p3) ∨ (((p4 → p4) → ((p5 ∧ p3) ∨ p4)) ∨ (p4 ∧ False))))) ∨ ((False ∧ p3) → (False ∧ (p5 → p2)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672607889278679604018896053073 : (((((p4 ∨ (p1 ∧ ((True ∨ (((True ∨ (p3 ∧ False)) ∧ False) → (False ∧ p5))) ∨ (p4 ∧ p1)))) ∧ (p2 → False)) → (p1 → (p5 → p5))) ∨ p1) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45363583996932272072738260076 : (((p4 ∧ (((((p3 → (p1 ∨ True)) → p4) → True) ∨ p5) ∧ (((p5 → ((p2 ∨ p1) ∧ (p2 → (p3 ∧ p2)))) → True) ∨ False))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165243919210372183038052221212 : (((False ∨ ((p4 ∨ ((p2 ∨ False) → p5)) ∨ (((False ∨ p2) ∧ p1) ∨ True))) ∨ (p2 → p4)) ∨ (((((p5 ∨ p1) ∧ False) → p1) ∧ p5) → p3)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66300166364920301966090966616 : ((p5 ∨ ((p1 → p4) ∨ (((p2 ∨ p2) ∨ ((p3 ∨ False) ∨ ((p2 ∧ p3) → (((p4 → (p2 ∨ p2)) ∧ p3) → p2)))) ∨ (p3 ∨ p1)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632280857610865024712705051742 : (((((p2 ∧ (((True ∧ (False ∨ True)) ∨ (p5 ∧ (p3 → ((False ∧ p5) ∧ p1)))) → (p1 ∨ (p2 ∧ ((p3 → p4) ∧ p5))))) → True) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246499381755823591695080469850 : ((p5 ∧ p1) ∨ ((p5 ∧ ((False ∨ p1) → (((p1 ∨ (p4 ∨ (False ∧ ((False ∨ (p1 → p5)) ∧ p3)))) → ((p4 ∨ False) ∧ False)) ∧ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_239156727284680612187501580767 : ((p2 ∨ True) ∧ ((p5 ∧ (p4 ∨ (True → ((p1 ∨ ((p5 ∨ ((p4 ∧ ((p1 → (p4 ∨ p2)) → (p4 → p3))) → p3)) ∨ False)) ∧ False)))) → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
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
theorem thm_5_vars_135865518031718717166151349422 : ((((((True ∨ p4) → (p1 ∨ False)) ∧ (False ∧ p1)) ∨ (False ∧ p5)) ∨ ((p3 → (False → (p2 ∧ p5))) → (p5 ∨ p2))) ∨ ((p4 ∧ False) → p5)) := by
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
theorem thm_5_vars_339844885290004071838192958320 : (p1 → (True → (((p4 ∧ (((p2 ∨ (((False ∨ ((p1 ∨ True) ∧ ((p2 ∨ p1) → p3))) ∨ p2) ∨ p3)) ∧ (p3 → p2)) → p2)) ∨ p3) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148181048261559839367126572281 : ((((p4 ∧ (((p3 ∨ p4) ∨ (((p5 ∨ False) ∧ p2) ∨ p2)) → p2)) ∨ (True ∧ True)) ∧ (p2 ∨ (p4 ∧ True))) ∨ (True ∨ ((True → p2) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56588622070001612688322179682 : (((p2 → ((p5 → True) ∨ p3)) → (p3 ∨ (((True ∧ ((p5 ∧ False) ∧ ((p4 ∨ p5) ∨ True))) ∨ (True → ((p2 → False) ∨ p5))) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262987364427610993523814523977 : (True ∧ (((((True → p1) ∨ (p1 → (((False ∧ p5) → (p3 ∧ (p3 ∧ p1))) → (p3 ∨ p3)))) → (p1 → p2)) → (p2 → p2)) ∧ (False → p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



