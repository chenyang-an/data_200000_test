variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136466304962078617140155664494 : ((((p2 ∧ p3) ∧ p1) ∧ ((p2 → ((p1 ∧ (p4 → False)) ∨ (p4 → p3))) ∨ ((p3 ∧ ((False ∨ p1) → True)) ∨ p1))) ∨ ((True ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704478215499690814840100668190 : (((((p3 ∨ (p3 ∨ False)) → (p1 ∧ ((p3 → p4) → False))) → ((p1 ∧ (False ∨ p4)) → (p4 ∨ (p3 ∧ (((p3 ∧ p3) ∨ False) → False))))) ∨ p5) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47466519814141674755491329300 : (((p5 ∧ (((((p1 ∨ False) ∨ p2) ∨ p3) ∨ (False → (p1 ∨ True))) → ((p1 ∨ (p4 ∧ ((p1 → p4) ∨ p1))) ∧ p3))) ∨ (True ∨ p1)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42420329895896922623564339035 : (((p5 ∧ ((((p2 ∨ (((((p2 → p2) ∨ ((p5 ∨ False) → p2)) ∨ p3) ∨ p3) → p4)) ∧ (p1 ∧ p1)) → p3) → (p3 ∨ p4))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159083337721641765731436679337 : ((True → ((p2 ∧ ((((p1 ∨ (False ∧ (False ∧ p4))) → (p5 ∨ p3)) ∨ p5) → (p1 → p3))) ∨ True)) ∨ ((((p5 ∨ p3) ∧ p1) ∧ p3) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249119198375722219736920094682 : ((p4 ∨ p2) ∨ (((((p5 ∨ (p2 ∨ (False ∧ True))) → (p3 ∨ ((p3 ∨ ((p2 ∧ p5) ∨ (False ∨ p1))) → p4))) ∨ True) ∨ False) ∨ (False ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246243170975618148926326696904 : ((p4 ∧ p3) ∨ (p2 → (((p4 ∨ (((p2 ∧ ((False → p3) ∧ p3)) → p3) ∨ (p1 ∨ (((p1 ∨ (p3 ∧ p4)) ∨ p1) → False)))) → False) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191303082799883170131548106091 : (((p2 → p4) ∧ ((p5 ∨ ((p3 ∨ p3) ∨ p5)) ∨ p3)) ∨ (((((False ∧ p4) ∧ p2) → p4) ∧ ((p2 ∧ p1) → p3)) ∨ ((p2 → p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157646045362840268165507220647 : (((p2 → (False ∧ ((p1 ∧ (p1 ∧ (((p3 ∧ False) ∨ p1) → p3))) ∧ False))) ∧ (p2 → (p4 ∨ p4))) ∨ (False → (p3 ∨ (p1 ∧ (p3 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309657465379626009931577119344 : (p2 ∨ ((p5 ∨ (False ∧ (((((p1 ∧ p2) ∧ ((p1 ∧ (p4 ∧ p5)) → (p4 ∨ (p2 → True)))) ∨ p4) → p4) ∧ p4))) ∨ (False → (True → p5)))) := by
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
theorem thm_5_vars_213484649367836343170799739404 : (((p1 → (p2 → p3)) ∧ True) ∨ (((((p2 ∧ ((False ∨ p4) → p5)) ∧ ((((p4 → p1) → (p1 → p2)) → True) ∨ p2)) → p3) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345381165406248307428998362271 : (p3 → (((p2 ∧ ((p4 ∧ ((False ∧ p5) → p1)) ∨ (((p3 ∨ (True ∨ (False → (p1 ∨ (p4 ∨ p4))))) ∨ p1) → (p4 → p5)))) ∨ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45972244764057680018932481437 : (((p5 → (p4 → (((((p1 ∧ p2) ∧ ((False → ((p2 ∨ p1) → p5)) ∧ ((False ∧ (p4 ∧ p3)) ∧ p2))) ∨ p2) → p1) → True))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158524456514177486191410261593 : (((p4 ∨ p5) → (((True ∧ p3) ∧ (((p5 ∧ (((p1 → p5) ∨ False) ∧ True)) ∨ p4) ∧ True)) ∨ True)) ∨ (p3 ∧ (True ∨ ((p2 → p1) ∨ p2)))) := by
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
theorem thm_5_vars_42335389122492249657474707134 : (((p3 ∧ ((p1 → ((p1 → (((((p3 ∧ (((p2 ∨ p2) ∧ p3) ∨ (False ∨ p3))) ∨ p3) ∨ False) ∧ True) ∨ True)) ∨ p4)) ∨ p3)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113984930173946354759039814373 : (((p4 ∨ ((p2 ∨ (((False → (p4 ∨ (p2 ∨ p2))) ∨ ((False ∨ (False ∧ True)) ∨ p1)) ∨ False)) ∧ False)) ∧ ((p4 ∧ False) ∧ p5)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112298945715990786123990987692 : (((p1 → ((((p4 → (p2 ∧ (True → (p1 ∧ p1)))) ∧ (p2 ∧ p3)) ∧ p5) ∨ (p2 ∨ ((p5 ∨ (p2 ∨ False)) → p4)))) ∨ True) ∨ (p4 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45554179267034502366730273832 : (((p2 ∨ ((p1 ∨ ((False ∨ (p1 ∧ ((p5 ∧ p5) ∨ p3))) → (p4 ∨ (((False ∧ (p4 ∧ p2)) ∨ p4) ∧ p1)))) → (True → p3))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171595503517759510689411678066 : (((((p4 → p5) ∨ ((p1 → (p4 ∨ p5)) ∨ p5)) → (False ∧ (False ∨ p5))) ∨ p5) ∨ (p1 ∨ ((p5 ∨ False) → ((p4 ∨ True) ∨ (p5 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_918576824886305299622430442262 : ((((((True ∨ (True ∨ (((p2 → p3) ∧ p3) → p5))) → (p1 → False)) ∧ p1) ∧ ((((p4 → ((p5 → False) → False)) ∧ False) → p5) ∧ True)) → p4) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : (True ∨ (True ∨ (((p2 → p3) ∧ p3) → p5))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h8
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648913948749780934386156190872 : ((((((((True → (p5 ∧ (((p3 ∨ p5) → p5) ∧ p1))) ∨ (((p4 ∧ True) → p4) → (p2 ∧ p3))) ∨ p1) ∨ p1) → p2) ∧ (p2 → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186339174458691235416085188963 : ((((p4 ∧ (p5 → (p2 → p4))) → ((p1 ∨ p3) ∨ True)) → p3) → (p3 ∨ (((p4 → False) → p1) ∨ (((True ∨ p5) → (p4 → p1)) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∧ (p5 → (p2 → p4))) → ((p1 ∨ p3) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41837479903542834122014413269 : ((((p5 ∧ (p2 → p4)) ∧ (True ∧ ((((((p2 ∧ p4) ∧ p3) ∨ False) ∨ p1) → (p4 → ((p4 ∧ (False → p1)) ∧ False))) ∨ p5))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52479636089541494582397988864 : (((True → ((False ∨ (False ∨ ((p2 ∨ p5) ∨ p2))) ∧ (True → (p1 ∧ p3)))) ∧ (p1 ∧ (p5 ∧ ((((True ∨ p1) ∧ False) ∧ p1) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219411250865381582620459052206 : ((p3 ∨ (p3 → (True ∧ p4))) → (((p2 → p5) ∨ p1) ∨ (p3 ∨ (False → (((p2 → (((p4 ∧ p1) ∨ p2) → p4)) → (p3 ∧ p1)) → True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113409907286436249855987988897 : ((((((((((p1 ∨ p3) ∨ p1) ∧ p1) ∨ (p1 → (p2 ∧ True))) → (p1 → False)) → (p3 ∨ p4)) ∨ p4) ∧ p4) ∨ (p2 ∨ True)) ∨ (p2 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60083960709366755082236083461 : (((p2 ∨ p5) → ((p1 ∨ (p1 ∧ (True ∧ p1))) ∧ (p5 ∨ ((((p2 ∨ False) ∧ p2) ∧ p1) → ((p3 → p2) ∧ ((True ∧ p1) ∨ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326962889838880468301856350518 : (True → ((((p1 ∨ ((((p2 ∨ ((p1 ∧ True) ∧ p3)) ∨ (p2 ∧ p4)) → p3) ∧ ((p1 ∧ p3) ∧ p5))) ∧ (p5 ∧ p5)) → (p1 ∧ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198392064038092704852003388480 : ((p3 ∧ (p4 ∧ (p3 → (p1 → (p4 ∨ p2))))) ∨ (((p2 → p4) ∨ p3) → (p1 ∨ ((p2 → p2) ∨ (True ∧ ((p5 ∧ (p2 → p4)) → p1)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114783932086151949875311161626 : (((((p4 ∨ (((p3 ∧ (p5 ∧ (p5 ∨ True))) ∧ False) ∧ p5)) ∧ p3) → p2) ∧ (p1 ∧ (p3 ∨ ((p2 ∧ (p4 ∨ p3)) ∧ p3)))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768153786606949853947234823698 : (((p5 ∧ ((p1 → (((True ∧ (((p1 ∨ p3) ∨ p5) ∨ True)) ∧ (p5 ∨ ((p3 → ((True → p4) → p3)) ∧ p3))) ∨ p3)) ∨ (p2 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53304494238090674416705010685 : (((p4 ∨ (p2 ∨ (((p4 ∧ False) ∨ p4) ∨ (False → (True ∨ False))))) ∨ (((True ∧ p2) ∧ ((p3 ∨ (False ∨ p4)) → p2)) ∧ (p3 → p4))) ∨ p2) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321537989742108087723780119422 : (p4 ∨ (p2 → (((p5 → True) → (p2 → (True → (p1 ∧ (p5 ∨ (p3 → (True ∧ ((p4 ∧ (True ∧ ((p5 ∧ p5) ∨ p2))) ∨ p2)))))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42899737749896982886298936093 : (((p3 → ((True ∨ (((True → p3) → p2) → (p2 ∨ p1))) ∧ ((p4 ∧ ((((True ∧ True) → p3) → p1) ∧ p5)) ∨ (p1 ∧ p2)))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137845829238594615583563275193 : ((p3 ∨ (((p2 ∧ (p1 ∨ p3)) ∧ p3) ∨ (p4 → (((False ∨ (p5 → p1)) ∧ ((False ∧ p4) → p1)) → (True ∨ p4))))) ∨ ((p5 → p1) → False)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607125363043505914570566002308 : ((((((((p4 ∧ p1) ∧ False) ∨ (p1 ∨ (p2 ∨ p2))) ∨ ((p2 → (((p2 ∧ (True ∨ p4)) ∨ (False → p3)) ∨ p2)) ∧ p3)) ∧ p2) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301444929424326779054576063422 : (False ∨ ((True → ((p1 ∨ p3) ∧ p5)) → ((p4 → ((True ∧ (p4 → p3)) ∧ ((False → p5) ∧ (True ∨ ((False ∧ (p2 ∨ p1)) ∧ p5))))) → p5))) := by
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
theorem thm_5_vars_698494515697002135489207963959 : ((((((p3 ∨ False) ∨ (p3 → (p2 ∨ p5))) → (False ∧ (p3 → p2))) ∨ ((p5 → (p2 → (False ∧ p1))) ∨ ((False → (False ∧ True)) ∧ True))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193471598647264861771590460655 : (((p3 ∧ True) ∨ (((p2 ∧ (p3 → False)) → p3) ∨ p4)) → ((((False ∧ (p1 ∧ ((p4 → True) ∨ (p2 → False)))) ∧ (p4 ∨ p4)) ∨ p1) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
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
theorem thm_5_vars_263923858232054788830329369290 : (True ∧ (((((False ∧ (False ∧ p5)) → p3) ∨ p1) → ((p1 → False) ∧ (True → False))) → ((p2 ∨ p1) ∧ (p4 → ((p1 ∨ (p5 ∧ True)) ∧ p5))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False ∧ (False ∧ p5)) → p3) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : (((False ∧ (False ∧ p5)) → p3) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- False on the left can always be used.
    apply False.elim h13
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h15 := h1 h11
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
  have h17 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h16, we can now drive its conclusion.
  let h18 := h16 h17
  -- False on the left can always be used.
  apply False.elim h18
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h19 : (((False ∧ (False ∧ p5)) → p3) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h20
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- False on the left can always be used.
    apply False.elim h21
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h23 := h1 h19
  -- We need to get the right conjuct of h23 based on <expert-advice>.
  let h24 := h23.right
  -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
  have h25 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h24, we can now drive its conclusion.
  let h26 := h24 h25
  -- False on the left can always be used.
  apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145116652283526707017930053232 : ((((((p1 ∨ False) → p5) → p3) ∧ ((False ∧ p3) ∧ p2)) ∨ (p2 → (True ∨ (True ∨ (p5 ∧ (False → p3)))))) ∧ ((p5 ∧ p2) ∨ (False → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316780060364828534769882231164 : (p3 ∨ (True → (p1 → (((p2 ∨ (False → p3)) → (((p4 → ((p1 ∧ (p3 → ((p2 ∨ p4) ∧ False))) → False)) ∧ True) ∧ p5)) ∨ (p3 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41691405885126288147652801796 : ((((((p4 ∨ p5) ∨ (p4 → p4)) ∧ p2) → ((p4 ∨ ((False ∧ p3) → p2)) → ((p2 → p5) ∨ ((p4 ∧ (p5 → True)) ∨ p4)))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40455851914740404248461454044 : (((((((p5 → False) ∨ p4) ∨ p2) ∨ ((((p4 ∧ (False → p1)) → p5) → ((p1 ∨ p3) ∨ (p1 → False))) ∨ (p2 → p3))) ∨ True) ∨ False) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731593391437179733903773504711 : ((((p1 → (p2 ∧ p5)) → (((p1 ∨ False) ∧ (((p2 → p4) → (((True ∧ (p3 ∧ p4)) ∧ (p3 → p5)) → p1)) ∧ (p3 ∧ p2))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1133014419141115111286825159 : (((True → ((p3 ∧ ((p5 ∧ True) ∧ p4)) ∨ (True ∨ p5))) → ((((p4 ∨ p1) ∧ (False ∧ (True ∨ p2))) ∧ p2) ∧ (p1 ∧ p4))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → ((p3 ∧ ((p5 ∧ True) ∧ p4)) ∨ (True ∨ p5))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311218939185888357020377307971 : (p2 ∨ ((False → p2) → ((p4 ∧ (((p5 → p5) → p3) ∧ p4)) ∨ (p3 → ((((p3 ∧ False) ∨ (p5 ∧ False)) → (p3 → p5)) → (True ∧ True)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37497438373135355789094768225 : (((((True → (p5 → False)) → (p2 ∧ ((((p2 ∧ (p4 → (p2 → p5))) ∧ (p1 → p4)) ∨ False) ∨ (p1 ∧ (p2 ∧ p3))))) ∨ False) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644194516978021297402281775419 : ((((False ∨ ((((p3 ∨ (True ∨ (p4 ∧ (((p3 → p4) ∧ p3) ∨ ((((p4 → p4) ∨ True) ∨ p4) ∧ p3))))) → p1) ∧ True) ∧ p1)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76471223865941915324366089630 : ((((((True ∨ (p2 → p2)) ∨ ((p2 ∨ p4) ∨ ((p4 → (p5 ∨ (p5 ∧ p4))) → (p1 ∧ True)))) → p3) ∨ ((True ∨ p2) ∨ p1)) → False) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((True ∨ (p2 → p2)) ∨ ((p2 ∨ p4) ∨ ((p4 → (p5 ∨ (p5 ∧ p4))) → (p1 ∧ True)))) → p3) ∨ ((True ∨ p2) ∨ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75901364107005583585128575387 : ((((p3 → ((p3 ∧ p3) → (((((p3 → ((p2 ∨ p3) ∧ p4)) → p3) → (False ∨ (p3 → p2))) ∨ (p3 → p3)) ∨ p1))) ∨ False) → False) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 → ((p3 ∧ p3) → (((((p3 → ((p2 ∨ p3) ∧ p4)) → p3) → (False ∨ (p3 → p2))) ∨ (p3 → p3)) ∨ p1))) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138432163630813127087010042569 : ((p5 → ((((p5 ∨ ((p2 → (p2 ∨ (p3 ∧ False))) ∨ p3)) ∧ (p1 ∧ p2)) ∨ p1) → ((p2 → p3) ∧ (p4 ∧ False)))) ∨ ((p2 ∨ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81164706790264834320576778313 : (((p1 ∧ (p1 → ((p5 ∧ p5) ∧ (((p3 ∨ (((p3 ∨ False) → p2) → True)) → ((False ∧ True) → p1)) → p2)))) ∧ ((p2 ∧ False) → p2)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : ((p3 ∨ (((p3 ∨ False) → p2) → True)) → ((False ∧ True) → p1)) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h14 := h8 h9
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753170519228742228336268681352 : (((False ∧ (((((p3 → p3) ∧ p4) ∨ p2) → (p1 ∧ (False ∧ ((False → (p1 ∨ p1)) → (p1 ∨ ((p5 ∧ True) ∧ p1)))))) ∧ (True ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114396894631702315465944556616 : ((((((p2 ∨ (p5 ∧ ((p5 ∧ p1) ∧ p4))) ∧ p5) ∧ p2) ∨ (p5 ∧ ((p3 ∨ True) → p1))) ∨ ((p3 → (True ∨ p4)) ∧ p2)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42529182762731435836309242849 : (((p1 ∨ ((((((False → (p1 ∧ (True → p2))) → (((p4 ∧ (p1 → (p5 ∨ p1))) → p3) ∧ True)) → p5) → p1) ∨ p3) ∨ True)) ∨ p2) ∨ p3) := by
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
theorem thm_5_vars_149395318665264139549958684614 : ((True ∧ ((p3 ∨ (False ∧ (p5 ∨ (((((p3 ∧ (p3 ∨ True)) → False) ∨ p4) ∧ p2) ∧ (p5 → p1))))) ∧ True)) ∨ (True ∧ (p5 ∨ (True ∨ p1)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643733904444494046408145691974 : ((((p5 ∧ ((False → ((((True ∧ p4) ∧ True) → (True ∨ (((p2 → p3) → p4) → (False ∧ (False ∨ p3))))) → False)) ∨ (True → p3))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134347138927289907517344956379 : (((p5 ∧ (p3 ∧ ((((p4 ∧ p4) ∨ True) → (((p1 → p3) → True) ∨ p5)) ∧ (((p5 ∧ p4) ∨ False) ∨ p1)))) ∨ p2) ∨ ((True ∧ True) ∨ p1)) := by
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
theorem thm_5_vars_165252164696523074659692540346 : (((p2 → (((((p5 → p3) → (p1 → p3)) → p3) → (p4 ∧ p5)) ∨ True)) ∨ (False ∨ p5)) ∨ (((p4 → ((False ∧ p4) ∧ p2)) ∨ False) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166667298911891913020175474464 : ((p2 → (((p1 ∧ (p3 → p2)) ∨ (((True → (p5 ∨ (p2 → p3))) ∧ True) ∧ p2)) ∧ p1)) ∨ (((p5 → p2) → True) ∧ ((p1 → p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254207708052030502017527515547 : ((p2 ∧ p2) → (((((((p4 ∨ ((p5 ∧ p3) → p2)) ∧ p3) ∧ (((p1 ∨ p1) ∨ p1) ∨ p4)) ∧ True) → (p5 ∨ (p5 ∧ p3))) ∧ True) ∨ p2)) := by
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
theorem thm_5_vars_164690453952789670177826441410 : ((((((p5 ∧ (((p1 → (True → p5)) ∨ p1) → (p3 ∧ p1))) ∨ p5) ∧ p4) ∨ True) ∨ p3) ∨ (((False ∧ (p5 ∨ p3)) ∧ (p2 ∨ p2)) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69194572527854061382071960717 : ((p5 → ((p3 → (((((p4 → p3) → True) ∧ (p5 ∧ False)) → False) ∨ p1)) → (((p3 → (p4 → (p1 → (p3 ∨ p2)))) → p2) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305190568547204005706820273269 : (p1 ∨ ((p4 ∧ ((((p3 ∧ ((p3 ∨ p2) ∧ False)) ∧ (True ∧ p5)) ∨ False) ∨ (((True → p1) ∨ p3) → False))) ∨ ((False → p4) → (True ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2927645030542288470178071138 : (((p1 ∨ p1) ∧ False) ∨ ((((p5 ∨ p1) → False) ∧ (False ∧ (False ∧ p1))) ∨ (((False ∧ p1) → p1) ∨ ((p3 → (False ∨ p2)) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_159822555355870009098235123145 : (((p2 ∨ ((p2 ∨ (p4 ∨ (p4 → (True ∧ (False → ((p3 ∧ p2) ∧ (p5 ∨ p4))))))) ∧ p1)) ∨ p5) → (False ∨ ((p5 ∧ (p3 → False)) → p5))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h20
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- One of the premise coincides with the conclusion.
          exact h21
  case inr h23 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h24
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- One of the premise coincides with the conclusion.
    exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82625763810578011129117874564 : ((((((False ∧ (True → p2)) ∨ ((p3 ∧ ((p4 ∨ (True → False)) ∨ True)) ∨ True)) → p1) ∧ (p5 → p1)) ∨ ((True ∨ (p4 → p2)) → False)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : ((False ∧ (True → p2)) ∨ ((p3 ∧ ((p4 ∨ (True → False)) ∨ True)) ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (True ∨ (p4 → p2)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46039939068717415529661056880 : ((((p2 ∨ (p5 → ((p2 ∧ (((((p2 → p4) → False) ∨ ((True ∧ (p1 ∧ False)) → p4)) ∨ False) ∧ False)) ∧ False))) ∧ False) ∧ (p2 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206310180251487773082300991986 : ((p1 ∨ ((False ∧ p5) ∨ (False ∨ p5))) ∨ (True → ((p1 → ((p3 ∧ False) ∨ ((p2 ∨ False) ∨ (True ∨ (p2 → p4))))) ∨ (p4 ∨ (p1 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112871224872516183925942349178 : (((((True ∨ p2) → p4) → (((p3 ∨ ((p4 ∧ p5) → p5)) → (p5 ∧ (((p1 ∨ p1) → True) ∨ False))) ∨ (True ∧ p2))) → p2) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166089902048858345857899283334 : (((p5 ∨ p2) → (p2 ∧ (((False ∧ p5) ∧ (((p4 ∨ p2) → False) → (p2 → True))) ∨ p5))) ∨ ((p3 ∨ (p1 ∧ ((p1 → p3) → p4))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136480370134894276259166500275 : ((((p5 ∧ p1) ∨ p1) ∧ ((((p4 ∨ p1) ∧ p3) → (p4 → (p5 ∨ ((((p4 → p5) ∧ p3) → p1) ∧ True)))) ∨ p4)) ∨ (p2 ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119334988303944789067990422607 : ((p3 → ((p1 ∧ (((p4 ∨ p5) → False) ∨ p1)) → ((((True → p5) ∧ ((p3 ∨ True) → True)) ∧ p4) ∨ (p4 ∨ (True ∧ p3))))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249882180534447393305585580627 : ((True → False) ∨ (p3 ∨ ((True → (p2 ∧ (((((((True ∨ p3) → p3) ∧ ((p5 ∧ (True ∨ p2)) ∧ p5)) → p1) ∨ p5) ∨ True) ∧ p1))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135748487121489951719095953347 : (((((p3 ∨ True) ∧ p5) → (((True ∧ p4) → False) → ((False → p2) → p4))) ∨ (p1 → (True ∧ (p5 → (p3 ∧ p3))))) ∨ (p5 ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37340886818955430432743180089 : (((((p1 ∧ (p1 ∨ (((p5 ∧ ((p5 ∧ p2) → ((p5 ∧ (p2 ∧ p4)) ∧ p2))) → p4) ∧ (p3 → (False ∨ p1))))) ∧ False) ∨ p4) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198334121186009684335723375523 : ((p2 ∧ ((False ∧ (False ∧ (p1 → False))) ∨ p1)) ∨ ((True → (p4 → p2)) ∨ (True ∧ (False → ((False ∧ ((p5 ∨ p3) ∨ p4)) ∧ (p1 ∧ p4)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343148590733722151269503051200 : (p2 → (((p2 ∧ p3) → p1) ∨ (False ∨ ((p4 ∨ p3) → ((False ∨ p5) ∨ (((True ∨ (True → (p2 → p4))) ∧ ((p4 → p3) ∨ p2)) ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54674275011367586302685514102 : (((((p4 ∨ (p4 ∧ (False → p2))) ∨ True) → p4) → (((((p3 → p5) → (p3 ∧ p2)) ∨ p3) ∨ ((p4 → p5) ∧ (p5 → p5))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787227323858564450805298829698 : (((p4 ∨ (False ∧ ((True ∧ (p2 ∧ (((p1 ∧ (p1 ∧ ((False ∧ (True → p5)) → (p5 ∧ (p5 ∧ p5))))) ∧ p3) ∧ (p5 ∧ p5)))) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304003842511764956248810052784 : (p1 ∨ (((True ∨ True) → ((p3 ∨ (((p5 ∧ (p1 ∧ p1)) ∧ (False → (p2 ∧ (False → ((p3 ∨ (p2 ∧ False)) ∧ p2))))) ∧ p1)) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318609659190042187014934670542 : (p4 ∨ ((((False ∨ (p5 ∨ p2)) ∨ False) ∨ ((p4 → p2) → ((((p2 ∨ p5) → (p2 ∨ (p5 ∨ p5))) ∧ (False ∧ True)) → p2))) ∨ (p1 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705627796776856016798122342752 : (((((p1 → (p1 ∨ (False → (p2 → p2)))) → True) ∧ ((p4 ∧ (((p2 ∧ p5) ∨ p4) ∨ (((p5 → (p4 ∧ p3)) → p5) ∧ True))) ∨ True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249414559899286834734366158488 : ((p5 ∨ False) ∨ ((False ∨ (p1 ∧ ((p5 → (((False ∧ p4) ∧ ((p3 → ((p1 → ((p1 ∧ p4) ∨ p4)) → p5)) → p2)) → False)) ∧ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264999352728015458516718578842 : (True ∧ ((p2 → p2) → (((((((p2 ∨ p1) ∨ ((False ∨ p3) → ((p1 → (False ∧ False)) → (p2 ∨ p2)))) ∧ p3) ∧ p2) ∨ True) ∨ p5) ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135833500035859656315761579623 : (((((True → p2) ∧ p1) ∨ ((p1 → (p4 ∨ (p5 ∨ p4))) → p1)) ∧ (((True ∧ p4) ∧ (p3 ∧ (p5 → False))) ∨ p4)) ∨ ((p5 ∧ False) → p1)) := by
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
theorem thm_5_vars_802594856495909978762701130922 : (((p2 → (p5 ∨ (((p3 ∧ False) ∧ (p3 ∨ p1)) ∨ (((p3 ∧ ((p1 → p2) ∧ ((p3 ∨ p4) ∧ False))) ∧ ((False → True) ∨ False)) → p3)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
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
    apply False.elim h10
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180399138149032682535150235349 : (((p5 ∧ (False ∨ (True ∧ ((p4 → p1) → (True ∨ p3))))) ∨ (True → p4)) → ((((True → p1) ∨ p1) → (((True → True) → p4) ∨ p5)) ∨ True)) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63154863321407575616304363048 : ((p5 ∧ (((((True ∧ False) ∨ p1) ∨ False) ∧ (p3 ∨ (((((p5 ∧ False) → (False ∨ False)) → p3) ∨ (True ∨ p2)) → p3))) ∧ (p2 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250098945202806238832191507679 : ((True → p4) ∨ (((((False → (False ∨ ((((p2 ∧ p3) ∨ p1) ∨ p5) ∨ p2))) → False) ∧ p5) ∧ p1) ∨ (p1 → ((False ∧ (p4 ∧ p4)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50360227232705141742116963024 : (((((p5 → p3) ∧ p5) ∧ ((p1 ∧ (p4 ∧ (p4 ∧ False))) ∨ ((((False ∨ p3) ∧ p5) ∨ False) ∧ True))) ∨ (((p1 → p5) → True) → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337540180362730972569859587748 : (p1 → (((((p4 ∧ (p4 → True)) ∨ p2) ∨ p2) → ((False ∧ (p2 → (p5 → (True → False)))) ∧ (False ∨ True))) ∨ ((p5 ∧ (True ∨ p1)) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180418688457244209260163747680 : ((((True → ((p4 → p2) ∧ (p3 ∨ (p5 ∨ False)))) ∧ p3) → (p5 ∧ p3)) → (((p2 ∨ (p5 ∨ p4)) ∨ (((p2 ∨ False) ∨ True) ∨ False)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221917256889739866775200813550 : (((p5 ∧ p1) → p5) ∧ (p1 → (p1 ∧ (((((((True ∧ False) → (p2 → p1)) ∨ p3) ∨ (p4 ∨ p4)) → (p4 → p2)) → p4) ∨ (p1 → p1))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327027362849796808545709128772 : (True → ((((p5 → (((True → p4) → p2) ∨ p1)) → ((p5 ∨ p2) ∨ p1)) ∨ ((p4 ∧ False) → (((p1 ∨ False) ∨ (True ∨ True)) ∧ p1))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_551351638149229949632569373741 : (((p1 ∨ ((p1 ∧ ((False ∨ p3) ∨ True)) → (p2 → ((((False → ((True ∧ p1) → True)) → (p5 ∧ False)) → False) ∨ ((p5 → p3) → True))))) ∧ True) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322410083366481660750057935868 : (p5 ∨ (((((p3 → (p3 ∧ (p2 ∨ False))) ∧ p3) → (True ∨ p5)) ∧ ((p4 ∧ False) ∨ ((p1 ∨ ((False ∨ p2) → (p5 ∧ p3))) ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179976538319782474583141889767 : ((((False ∨ ((p1 ∧ p1) ∧ True)) ∧ ((p4 ∧ False) → (True ∧ p4))) ∨ p2) → (((p5 → (False ∧ p2)) ∧ ((p3 ∧ p4) → (p2 ∧ p3))) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321624698496591524251748061629 : (p4 ∨ (p3 → ((p4 ∧ (p2 ∧ (p2 ∧ p4))) ∨ ((p3 → ((False → p3) ∨ ((p1 ∨ True) ∧ ((p3 → (p3 ∨ p2)) ∧ p4)))) → (p2 ∨ True))))) := by
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



