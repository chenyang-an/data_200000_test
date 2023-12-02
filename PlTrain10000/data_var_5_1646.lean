variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40387364963247864397996546454 : (((((p4 ∧ (((p2 ∨ (p1 ∨ p2)) → p2) ∧ ((p4 ∧ ((p2 → (True ∧ (p1 ∨ p5))) ∧ False)) → p5))) ∨ (p4 ∨ p3)) ∨ False) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255981980171966861291728624880 : ((True ∨ p3) → ((((((p1 ∨ p4) ∧ p1) → (((p4 ∧ True) ∨ ((p1 → (False ∨ p4)) → p3)) ∧ p4)) → p5) ∨ (p1 ∨ p1)) ∨ (False → False))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112306366182798046492906541699 : (((p2 → ((((p2 ∨ (False ∧ (p1 ∧ p5))) ∨ (((p5 ∨ (p5 → (p3 ∧ p3))) ∧ False) → False)) → (p5 ∧ p1)) ∨ p4)) ∨ True) ∨ (False ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209590005190811631229492769686 : ((p5 → (True → ((False ∧ p5) → p3))) → ((p1 ∧ True) ∨ (((((p3 ∨ p2) ∧ (p2 → (False ∧ p4))) → (p1 ∨ p3)) ∨ True) ∨ (p2 ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157784447901101750588411223895 : (((((False ∨ (p1 → (p5 ∧ p4))) → False) ∧ (p1 ∧ (False → p4))) ∨ (((p4 → p4) ∨ False) ∨ p4)) ∨ (p2 ∧ (p4 ∨ (p4 ∧ (p5 ∧ p5))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39647904365302410711556042916 : (((p3 ∨ (((((p3 ∨ p3) → (True ∨ p3)) ∧ (True ∧ p1)) ∧ p2) → ((p5 ∧ ((False → p4) ∧ (p1 ∧ True))) ∧ (p2 → p3)))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167654695374600090921084145083 : ((((True → p5) ∨ (((p5 ∨ (p3 → (p4 ∧ p1))) ∨ (p5 → p1)) ∧ p1)) → (True → False)) → (p1 → ((p5 → False) ∧ (p1 ∧ (p1 ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : ((True → p5) ∨ (((p5 ∨ (p3 → (p4 ∧ p1))) ∨ (p5 → p1)) ∧ p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h4
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : ((True → p5) ∨ (((p5 ∨ (p3 → (p4 ∧ p1))) ∨ (p5 → p1)) ∧ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h9
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h12 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h13 := h11 h12
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53977590839860565686042249092 : ((((((p5 ∧ p4) → ((p1 ∨ True) → p4)) ∧ p5) ∨ False) → ((p2 → (False → True)) → ((p2 ∨ (((p5 → p4) → False) → p3)) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50257596155949549855441232805 : ((((p2 ∨ (((True ∨ ((p5 ∨ (p3 → p2)) → (False ∧ True))) ∨ p3) ∧ (p3 → (p4 ∨ p3)))) → p1) ∨ (((True → p3) ∨ True) ∨ p2)) ∨ False) := by
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
theorem thm_5_vars_49258375968116522295110495358 : (((False ∧ ((p2 ∨ p3) ∨ (p3 ∨ ((p5 ∧ p5) → (p4 ∨ (False → (((p3 ∨ p5) ∨ (p1 ∨ p1)) ∧ p1))))))) ∨ (False → (p2 ∨ True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191666989116067760347101808101 : ((p5 ∧ ((True ∧ (((p3 ∧ p2) → True) → p2)) ∨ p3)) ∨ (((p1 ∨ (((p4 → p3) → p3) ∧ (p5 ∨ (True ∧ (p2 ∧ p4))))) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248849250965921905573374971478 : ((p3 ∨ p4) ∨ (p2 ∨ ((False ∧ ((p3 ∨ ((p3 ∨ p2) ∧ p2)) ∨ False)) ∨ (p1 ∨ (((p4 ∧ p5) → (True ∧ p5)) → (p5 → (p5 → p5))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791948035780400162646419408293 : (((True → ((p3 ∧ (p4 ∧ ((p2 ∨ (p5 ∨ p4)) ∨ (False ∧ ((((False ∧ (p2 → True)) → True) → p2) ∨ (p5 ∨ p3)))))) ∨ (False → p4))) ∨ False) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792368082828955331219716432454 : (((True → (((True ∧ (False ∨ (p3 → (((True ∨ (p2 ∧ False)) ∧ p1) ∨ p4)))) ∨ True) ∨ ((p5 ∨ p1) → ((False → (p4 → True)) ∧ p3)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723846265539481806806661544954 : (((((p5 → p1) → True) ∧ (p4 ∨ ((p1 ∧ ((True ∧ False) → (((((p5 ∧ False) → False) ∨ (p1 ∧ p2)) → (True ∧ False)) ∨ False))) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214403969148417179945312161671 : (((p1 → (p4 ∧ False)) → p3) ∨ (p4 → ((p3 ∧ (((p4 ∧ p4) → (p5 ∨ (p5 → (False → p5)))) → p5)) ∨ ((p3 ∧ p5) ∨ (True ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_358471187612458296772158205495 : (p5 → (p1 → (((p4 ∨ (p1 ∧ ((p4 ∨ (False ∧ (p5 → p2))) ∧ True))) ∨ (p3 ∨ (((p4 ∨ p3) → p4) ∧ (True ∨ False)))) ∨ (False → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4095765512079516484930798245 : (p3 ∨ ((((p1 → (p3 ∨ (((((p4 ∨ p3) → True) ∨ ((p1 ∧ p1) ∧ (p3 ∨ p3))) → p5) ∨ p3))) ∨ True) ∧ True) ∨ (p1 ∧ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113458104986784854638685536566 : (((((p3 → ((((p3 ∧ True) ∨ ((p3 ∨ (p5 ∧ p3)) ∨ p1)) ∨ p5) ∨ (p4 ∨ True))) ∨ (True → p2)) → p3) ∨ (True ∧ True)) ∨ (p5 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60073270705410442718356337730 : (((p2 ∨ p3) → ((p1 ∧ p2) ∨ (((True ∧ (p3 ∨ (((p2 ∧ False) ∨ p2) ∨ (p3 ∨ p5)))) → p1) → (p2 ∧ (p4 → (False ∨ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_913980800349528241519258791225 : ((((((((p3 ∧ p4) → p1) ∧ p2) ∧ (True → (((True → True) ∧ p2) ∧ False))) ∨ p5) ∧ (((p2 ∧ (False ∨ False)) ∨ (p2 ∧ p4)) → True)) → p5) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198748255460308241212988482093 : ((True → ((((p4 ∨ True) ∨ p2) → True) → p4)) ∨ (p5 ∨ ((False → p4) ∨ (((p4 ∨ ((p3 → True) ∨ (p2 → (p4 → p5)))) ∧ False) ∨ p3)))) := by
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
theorem thm_5_vars_62714514622044863387357424394 : ((p4 ∧ ((p2 ∧ ((p5 → p5) ∧ ((p3 ∧ p2) → (False → ((False → False) ∧ ((p5 ∨ (p4 ∧ p2)) ∨ (p2 → (p5 → p1)))))))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206151355396000485038675379984 : ((p5 ∧ ((p1 ∧ (False ∧ p5)) ∧ p2)) ∨ (p3 → (p3 ∨ ((False ∨ (p1 → (p4 ∧ (p1 ∧ (((p5 ∧ (p1 ∨ p3)) → False) → p3))))) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751154030475566685140406344398 : (((True ∧ (((True ∧ p1) ∧ p3) ∨ ((p3 ∨ ((p5 → p3) ∨ (((p3 → (((p3 ∧ p2) ∧ p3) → p3)) → p3) ∨ False))) ∨ (p3 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136338476018932743686476376330 : (((p3 ∧ ((p3 ∧ True) ∧ False)) ∧ ((((((True ∧ p5) → p1) ∨ p3) ∨ (False → ((p4 ∧ p5) ∨ p5))) → p5) ∨ False)) ∨ (p2 → (p2 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173328917413323500658186482650 : ((p2 → ((p3 ∧ ((p3 ∨ True) ∧ (True ∧ False))) ∨ (p5 → ((p3 ∧ False) ∧ p2)))) ∨ (((True → (p5 ∨ ((p5 ∧ True) ∧ p5))) → True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115873872513270473037481839591 : (((((True ∧ p5) → True) ∧ False) ∨ (((p2 ∨ ((p1 ∧ p1) → False)) ∨ ((p2 ∨ p4) ∧ (((True ∧ p5) ∧ p2) ∨ p1))) → p2)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148225903108696893557829092418 : ((((p5 ∧ (((p5 ∨ p2) → (((True ∧ (False → True)) → p2) → p5)) ∨ p5)) ∨ p3) ∨ ((p3 ∨ p3) ∧ p1)) ∨ (((False → True) ∨ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25156887464492472617492263518 : (((p4 → (p4 ∧ p3)) ∨ (((p2 ∨ p2) ∨ (((True ∧ p4) ∧ p4) ∧ p3)) ∨ (((((True → p5) ∨ p1) ∧ (p1 → p5)) ∧ p3) ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_117042198732919780392566634072 : (((p3 ∨ p4) → (p3 ∧ (((p5 ∧ (p3 ∧ ((False ∧ p5) → p3))) → p4) ∧ ((((p4 ∨ (False ∧ p3)) → p2) → p2) ∨ True)))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257975385998107196543476178022 : ((p4 ∨ p1) → (((p5 ∧ ((((p5 → False) → (p4 → p3)) ∧ p1) ∧ (p1 ∧ p3))) ∧ (((False ∧ (p2 → False)) → (p2 ∨ p5)) ∨ False)) ∨ True)) := by
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
theorem thm_5_vars_53816819968687240952222592045 : ((((p3 ∨ ((True ∨ p1) ∧ (p2 ∨ p5))) ∧ (True → False)) ∨ (p2 → (p1 ∧ (((p2 → ((p5 → p5) ∨ (p1 ∨ p1))) → p2) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201991725981829040176390268285 : (((p3 → ((p3 → p1) ∨ p2)) ∨ True) ∧ (((True ∧ p2) ∨ p5) → (((p2 ∧ p4) ∧ (p1 → (p4 ∧ True))) ∨ ((True ∨ (p2 → p2)) ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111876925700342979661665574723 : ((((((((p2 → True) → True) → p2) ∧ (False ∧ (p4 → ((p2 ∧ True) ∧ p3)))) → True) → (((True ∨ p4) ∨ p4) ∧ p4)) ∨ p3) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348813581213087389315419823104 : (p3 → (p1 ∨ (((p1 ∧ p3) ∧ (p5 ∨ ((p3 → p5) → True))) → (((p2 ∧ p4) ∨ True) ∨ ((((False ∨ p5) ∨ (True → p2)) ∧ p4) ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40962574646245823243237355217 : (((((False → (p5 ∨ (True ∨ (p5 → (False ∨ (p4 → True)))))) ∧ ((p1 ∧ (p2 ∧ ((True ∨ p1) → p2))) ∨ p1)) ∨ (p3 ∧ p1)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263898098680114012955400135398 : (True ∧ (((p5 ∨ p3) ∧ (p4 ∧ ((((p4 → p5) → (p3 → p2)) → p3) → False))) ∨ (p2 ∨ (False → ((False ∨ (p2 → (p4 ∧ False))) ∨ p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41820941683022211256615058564 : (((((True → p4) ∨ p1) ∧ ((((p4 → (False ∧ False)) ∧ (((p3 → p2) ∧ True) ∨ p3)) → (False ∨ ((p4 → False) ∧ p3))) ∨ p4)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14829879684435328881413462557 : (((((p2 ∧ ((p1 → (p4 → (p2 ∧ (False ∨ p1)))) ∨ p5)) ∨ p2) ∨ (p5 ∨ (((p4 ∨ (p4 ∨ p3)) ∧ p4) ∨ True))) ∨ (True → False)) ∧ True) := by
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
theorem thm_5_vars_683891349904776117768888561687 : (((((True → ((p2 ∧ ((True ∧ False) → (((p5 ∨ (p4 ∧ True)) ∧ p2) → p5))) → p5)) ∨ p5) ∨ (p1 ∧ ((p3 → True) ∨ (p4 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137682693511287382561908744239 : ((p1 ∨ (((p1 ∧ (((p4 ∧ p4) ∨ p1) → ((True ∨ (p4 ∧ (True → (p3 ∧ (p1 → p2))))) ∧ False))) ∧ p3) ∨ False)) ∨ ((p2 ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621138976161270629151704158278 : (((((p5 → False) → (((((p5 → p5) → True) ∨ ((p1 ∧ p5) → (p4 ∨ p3))) ∨ True) → ((p4 ∨ p2) ∨ (True ∨ (True → p5))))) ∨ False) ∨ p1) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
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
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37298231170663328767930467894 : ((((True → ((p3 ∨ p4) ∨ ((p4 → ((((p5 → p5) → False) → (p4 → ((True ∧ p1) → False))) ∧ (True ∨ p2))) ∧ p4))) ∧ False) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640652741315017276158356606024 : (((((p3 ∨ True) ∧ (((True ∧ ((((p1 ∨ p3) ∨ ((p1 ∨ p2) ∨ False)) ∨ (p2 ∨ (p5 ∨ (p3 → p5)))) → p4)) ∨ p2) ∨ False)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160269786852591810653430581186 : (((p1 → (((False → ((p3 ∧ p5) ∨ p2)) → ((False ∧ p5) ∧ (p5 ∨ True))) ∧ p2)) ∨ (True ∧ p2)) → (p1 ∨ (((True → False) ∧ False) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698319979086887267487077894032 : (((((p5 → (((False → (False ∧ False)) ∧ True) ∧ p1)) ∧ (p4 → p2)) ∨ (((True ∨ ((p4 ∨ False) ∧ True)) → p4) → (p5 → (p2 → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704329565534397642232605174816 : (((((False ∨ (p4 → (False ∨ p1))) ∨ ((False ∧ p2) → p5)) → (((True ∨ (True ∨ ((p3 ∧ (p1 → p4)) ∧ True))) → p4) ∨ (p5 → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245251430757291913689148698413 : ((p2 ∧ p1) ∨ (((p4 ∧ p4) ∨ p4) ∨ ((p1 → (p2 ∨ False)) ∨ ((p2 → (p1 → ((p5 → p2) ∨ p5))) ∧ (True ∨ (p4 ∧ (p5 ∨ p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263997526446654262106174057937 : (True ∧ ((p5 → (((p4 ∧ False) → ((p5 ∧ p2) ∧ p1)) → (False ∧ p1))) ∨ (p1 → (p3 → (((((True ∨ p1) ∧ False) → p5) ∨ p3) ∨ p5))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121783407861291581016066950616 : (((((p1 ∧ True) ∨ False) ∨ ((((((p2 ∨ p2) ∧ (p3 ∧ (p1 ∨ (True → (False ∧ False))))) → False) ∧ True) → False) ∨ p3)) → False) → (p3 → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p1 ∧ True) ∨ False) ∨ ((((((p2 ∨ p2) ∧ (p3 ∧ (p1 ∨ (True → (False ∧ False))))) → False) ∧ True) → False) ∨ p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709724692754239751663496853284 : ((((True → (False ∨ ((True ∧ (True ∨ p4)) ∧ p3))) → ((((p4 ∧ (p1 → p5)) ∨ (p1 ∧ (p5 → True))) ∨ True) → ((p3 ∨ True) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327064770894512631561602001401 : (True → (((p1 ∨ ((True ∨ p3) ∨ p1)) ∧ (p3 → ((((p3 → ((p5 ∨ (p1 ∨ (p2 ∧ (True ∨ False)))) ∨ p3)) ∧ p4) ∧ True) ∨ p3))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621736052735043081122525606228 : ((((p1 ∧ ((p5 → (p4 ∨ (False ∧ (p4 ∧ (((False ∨ p1) ∨ (p2 → ((p3 ∨ True) ∧ (True ∧ (True ∧ p5))))) → p1))))) ∧ p3)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_652079968047596138010757218639 : ((((False ∧ (p4 ∧ ((p5 ∨ (p1 → (((p3 → (p4 ∧ p3)) → p4) ∧ (p2 ∧ p4)))) ∧ (p5 → ((p4 ∨ p3) ∨ p3))))) ∧ (False ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125341156548117903453229404464 : (((p1 ∨ (False → p2)) → ((True ∧ ((False → (((p5 → p1) → p3) → (p1 ∨ p4))) → False)) ∧ (p3 ∨ ((p4 → p3) ∧ False)))) → (p4 ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ (False → p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (False → (((p5 → p1) → p3) → (p1 ∨ p4))) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h10 := h6 h7
  -- False on the left can always be used.
  apply False.elim h10
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : (p1 ∨ (False → p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- False on the left can always be used.
    apply False.elim h12
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h11
  -- We need to get the left conjuct of h13 based on <expert-advice>.
  let h14 := h13.left
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
  have h16 : (False → (((p5 → p1) → p3) → (p1 ∨ p4))) := by
    -- Implications on the right can always be decomposed.
    intro h17
    -- Implications on the right can always be decomposed.
    intro h18
    -- False on the left can always be used.
    apply False.elim h17
  -- We have shown the premise of h15, we can now drive its conclusion.
  let h19 := h15 h16
  -- False on the left can always be used.
  apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636470754953340934168435219676 : ((((((((p4 → ((p5 → p5) ∨ ((False ∨ p2) → False))) ∧ False) → p1) ∨ p3) ∧ (False → (((p3 → p3) ∨ (p4 ∨ False)) ∨ p2))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793943441266303701853857188266 : (((True → (p5 → ((((True → False) ∧ p3) ∨ p5) → (((False ∧ (p4 ∨ p3)) ∧ (False → (p3 ∧ (p1 ∧ p2)))) ∧ (p5 ∧ (p3 → p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730078823768802800395134803975 : (((((p2 ∨ p3) → p3) → ((True → (p4 ∨ (((True ∨ False) ∨ (((p1 ∧ (p2 ∧ False)) ∨ p5) → True)) ∧ p5))) ∨ (p5 ∨ (False → p4)))) ∨ p1) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44539491746249773165596402111 : (((((p1 ∧ p2) ∧ ((((p1 ∨ p5) ∨ p5) ∧ p2) ∧ p4)) → ((False ∧ p2) → ((p1 ∨ (p5 → (False ∧ p2))) ∨ (False → False)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208652356447848419327839341269 : ((True ∧ (p2 ∨ (p1 ∨ (False ∧ p1)))) → ((p5 ∨ (p2 ∧ p3)) ∨ ((((p3 ∨ p3) ∧ True) → (p4 ∨ (((False ∨ True) ∨ p2) → p4))) → True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
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
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354980283855146576950263253914 : (p5 → ((p5 → ((((p2 ∨ p2) ∨ (p5 ∨ p1)) ∧ p2) → (p2 → ((p1 → ((False ∧ True) ∨ (p3 → (False → p5)))) ∧ (p3 ∧ False))))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40292896239538087102018879080 : ((((p4 → (False ∨ ((p3 ∧ ((p5 ∨ ((((p1 → (p3 → p3)) ∨ (False ∧ (p1 → p5))) → True) ∨ False)) ∧ p1)) ∧ p2))) ∧ p2) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136212266713995431653248653382 : (((p5 → ((p3 ∧ (True → p1)) → p3)) ∧ ((p2 ∨ (p3 ∧ p1)) → ((p2 ∨ p5) ∧ (p4 ∨ ((p2 → p2) ∨ p1))))) ∨ (True ∨ (p3 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774831567890612995864048225943 : (((False ∨ ((((p3 ∨ p1) ∧ True) → p2) ∧ ((False → (p4 ∨ ((False → ((p2 ∧ True) ∧ (p2 → p3))) → ((p5 → p4) → p5)))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160036455612856146531503150698 : ((((p1 ∨ p4) ∨ (p1 → (((p2 ∨ (p4 ∨ p5)) → (False ∨ (True → (p5 ∧ p4)))) → p2))) → False) → (p2 → ((p3 ∧ p1) ∨ (p2 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p1 ∨ p4) ∨ (p1 → (((p2 ∨ (p4 ∨ p5)) → (False ∨ (True → (p5 ∧ p4)))) → p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h3
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198323437193451884389470017721 : ((p1 ∧ (False → ((p5 → p1) → (p3 ∧ p1)))) ∨ ((p5 ∨ (p5 → (((p2 ∨ ((p3 ∧ p1) ∨ p1)) ∨ (p2 ∧ True)) ∨ p5))) ∧ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259418177071375262509792003473 : ((False → p3) → (p4 ∨ (p3 → ((p2 ∧ ((False ∧ True) ∨ ((p3 ∨ (p5 ∧ p5)) → p4))) ∨ ((False → (p4 ∧ p4)) ∧ ((p4 → p3) ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720298000471750152715967246151 : ((((((False → p3) ∧ p5) ∨ p1) → ((p3 ∧ p2) ∨ (((p2 ∧ (p3 ∨ (p4 → (p2 ∧ p5)))) ∨ p4) ∨ ((p5 ∧ (False ∧ True)) → p5)))) ∨ p3) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- False on the left can always be used.
    apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318486078338644605086114377879 : (p4 ∨ (((((p3 ∨ (p3 ∧ (p3 ∨ False))) ∧ True) → p4) → ((p2 ∨ p3) ∨ ((p5 ∧ (p5 ∨ ((p5 ∧ p4) ∨ p1))) ∨ True))) ∧ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664874935110523551303062832155 : ((((p2 → ((True ∧ p3) ∧ ((p1 ∧ p2) → (p2 ∨ (p1 ∨ ((True ∨ (p1 ∧ p5)) ∨ (((p4 ∨ True) → True) ∨ p3))))))) → (p5 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181303578877986349663681221187 : ((p5 ∧ (p3 ∧ (p1 ∧ (p2 → (p4 ∨ (((True ∨ False) → p1) ∨ p4)))))) → ((((p3 → False) ∧ p4) ∨ p5) ∧ (p1 ∧ ((p3 ∨ False) ∧ p5)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h11.left
  let h13 := h11.right
  -- One of the premise coincides with the conclusion.
  exact h12
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h15.left
  let h17 := h15.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h17.left
  let h19 := h17.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h16
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h21.left
  let h23 := h21.right
  -- Conjunctions on the left can always be decomposed.
  let h24 := h23.left
  let h25 := h23.right
  -- One of the premise coincides with the conclusion.
  exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329148547189026959421219775431 : (True → (((p3 → (False → p2)) ∧ p4) → ((((p1 → True) ∨ True) → ((p2 ∨ (p4 ∨ (p4 ∨ p5))) ∧ ((p3 ∨ (True → p1)) ∨ p4))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677655582921863775491630663820 : ((((((p1 → (((((p3 ∨ p3) → ((p4 ∨ p3) → p4)) → p1) ∧ p4) ∨ True)) ∨ (p1 ∧ True)) → p3) ∨ (p2 ∧ ((p5 ∨ p3) → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2010819441764260066741684012 : (((True → (p3 ∧ p5)) ∧ (p5 ∨ (p3 ∧ (((p1 ∨ p2) ∨ (True ∨ False)) ∧ ((True → p2) ∨ False))))) → ((p5 ∨ (p2 ∧ p4)) ∨ p3)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h13 =>
          -- False on the left can always be used.
          apply False.elim h13
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h16 =>
          -- False on the left can always be used.
          apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h20 =>
          -- False on the left can always be used.
          apply False.elim h20
      case inr h21 =>
        -- False on the left can always be used.
        apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348842224481740390526328885437 : (p3 → (p2 ∨ (((((((((p5 ∧ (False → p5)) ∨ (p4 ∧ p4)) → True) → p2) ∨ (p4 → p4)) ∨ False) ∨ ((p5 → p3) ∧ p3)) ∨ True) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41122673959756503503190031454 : ((((p4 → (p5 ∨ ((p2 → ((p5 ∨ p1) → (p1 ∨ True))) → (p1 → ((p1 → False) ∨ (False ∧ True)))))) ∧ ((p3 → p4) ∧ p3)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801858347172658978638475597229 : (((p2 → ((False ∨ True) ∧ (((p3 ∨ (((((False ∧ p5) ∧ (True ∧ (p2 ∨ (p5 ∨ p3)))) ∧ p3) → p3) → p5)) ∨ (p4 ∨ p2)) ∧ p2))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165698077142451456124562710169 : (((p1 → ((False → (False ∧ p1)) ∧ p4)) → (p3 ∧ (p3 ∨ (True ∨ (True ∧ (False ∨ p2)))))) ∨ ((p5 ∧ ((p2 ∨ True) ∧ (False ∧ p5))) → p2)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h5.left
    let h11 := h5.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211206089132630403547324308374 : (((p5 → True) ∧ (True → True)) ∧ ((p3 ∨ (p5 ∨ ((False ∨ p3) ∨ (p3 ∨ ((p3 → True) ∨ ((False → p2) ∨ (p3 ∧ p3))))))) ∨ (p3 → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622619618211484305533427449717 : ((((p4 ∧ ((p2 ∧ ((p4 ∧ (((((True ∧ (p3 ∧ True)) → p3) ∨ (False ∧ p1)) ∧ False) ∧ (p2 ∨ p2))) ∧ True)) ∧ (p1 → p5))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_199550266950354158784267755121 : ((((True → (p2 ∧ (False → p3))) ∧ p1) → p4) → (((False ∨ True) → ((p2 ∨ p3) ∧ (((True → ((p4 → p1) ∨ p3)) ∧ False) ∧ p5))) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_863177368876948386332882327146 : (((((((p4 ∧ (p5 ∧ p5)) → (p5 → ((p5 ∨ (p1 ∨ False)) ∧ True))) → p4) ∨ (p1 → (p1 → (p5 → (p3 ∨ (p1 → p1)))))) → False) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p4 ∧ (p5 ∧ p5)) → (p5 → ((p5 ∨ (p1 ∨ False)) ∧ True))) → p4) ∨ (p1 → (p1 → (p5 → (p3 ∨ (p1 → p1)))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_91156428959864738995428613779 : (((p5 → False) ∧ ((((p2 ∧ ((p1 → p3) ∨ p3)) ∧ ((False → p2) → ((p2 ∧ False) ∧ p5))) ∧ (False → p1)) ∧ (p1 ∧ (p1 ∨ p4)))) → p5) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h5.left
    let h14 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h16 : (False → p2) := by
        -- Implications on the right can always be decomposed.
        intro h17
        -- False on the left can always be used.
        apply False.elim h17
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h18 := h9 h16
      -- We need to get the left conjuct of h18 based on <expert-advice>.
      let h19 := h18.left
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h22 : (False → p2) := by
        -- Implications on the right can always be decomposed.
        intro h23
        -- False on the left can always be used.
        apply False.elim h23
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h24 := h9 h22
      -- We need to get the left conjuct of h24 based on <expert-advice>.
      let h25 := h24.left
      -- We need to get the right conjuct of h25 based on <expert-advice>.
      let h26 := h25.right
      -- False on the left can always be used.
      apply False.elim h26
  case inr h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h5.left
    let h29 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h30 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h31 : (False → p2) := by
        -- Implications on the right can always be decomposed.
        intro h32
        -- False on the left can always be used.
        apply False.elim h32
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h33 := h9 h31
      -- We need to get the left conjuct of h33 based on <expert-advice>.
      let h34 := h33.left
      -- We need to get the right conjuct of h34 based on <expert-advice>.
      let h35 := h34.right
      -- False on the left can always be used.
      apply False.elim h35
    case inr h36 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h37 : (False → p2) := by
        -- Implications on the right can always be decomposed.
        intro h38
        -- False on the left can always be used.
        apply False.elim h38
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h39 := h9 h37
      -- We need to get the left conjuct of h39 based on <expert-advice>.
      let h40 := h39.left
      -- We need to get the right conjuct of h40 based on <expert-advice>.
      let h41 := h40.right
      -- False on the left can always be used.
      apply False.elim h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64825278663018682633074003523 : ((p2 ∨ ((((p5 ∨ (((p4 ∨ (p2 → p1)) ∨ (p2 ∧ p2)) ∨ (False → ((p4 ∨ p1) ∧ p1)))) → p5) → (p1 ∧ (p4 ∧ p5))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177849618962010516355560240671 : ((((p3 → ((p4 ∨ p2) → (p1 ∨ ((p1 ∨ p2) ∧ True)))) ∧ p5) ∨ p3) ∨ (((p4 → p4) ∨ (p3 → (((True ∧ p5) ∨ p3) ∧ False))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37355146181740900982731728086 : ((((((((((False → (p2 ∨ p5)) ∨ (p2 → (p1 → (p1 ∧ p5)))) ∨ (p1 → p2)) → p1) ∧ p3) ∨ (p5 → p5)) ∨ True) ∨ p2) ∧ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_642092859120670511563416790586 : ((((True ∧ (((((True ∧ (p3 ∨ (p3 ∨ ((p3 ∨ p1) ∨ p3)))) → p1) ∨ (p2 ∧ (p5 → p2))) ∧ p1) ∨ (p4 ∨ (p1 ∧ p1)))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135412544511034848056335988387 : ((((p3 → (p4 → True)) → ((p5 ∧ p4) ∧ ((p1 ∨ (False ∧ p5)) ∧ ((p3 ∨ p2) → p1)))) ∨ ((p4 ∧ p1) → True)) ∨ (True → (p2 ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322559563230828255191674773752 : (p5 ∨ ((p1 ∨ (p5 → (((p4 → ((((True → (p4 ∧ p1)) ∨ p5) → p1) → False)) ∧ p2) ∨ (((False → (p4 ∧ p5)) ∨ p4) → p5)))) ∨ p2)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233832909346225360550529179467 : ((p4 ∨ (False ∧ True)) → ((True → ((((False ∧ ((p3 → (False ∨ (True ∧ ((p2 ∨ p4) ∧ p3)))) → False)) ∨ (False → p3)) → True) ∧ p3)) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
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
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765703186079708077814026559278 : (((p4 ∧ (((False ∨ p1) ∨ (p2 ∧ (True ∧ ((p4 ∧ True) → p4)))) ∧ (((((True ∧ p4) ∨ p5) ∨ False) ∧ (True ∧ (p2 ∨ p4))) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349048611249557589698990575666 : (p3 → (p5 ∨ ((((p4 ∧ (((p4 ∨ False) ∨ (p2 → (p5 ∧ p4))) ∧ p4)) ∧ (True → (False ∨ p5))) ∧ p5) ∨ ((False ∧ False) ∨ (False ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301830658498299780764629353361 : (False ∨ ((p3 ∨ False) ∨ (((False ∧ False) ∧ ((p3 → False) → p5)) ∨ ((p3 ∨ (p4 ∨ (p4 ∧ p2))) ∨ ((True → False) ∨ (p5 ∨ (p1 → p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42621935239235710499362813238 : (((p3 ∨ (((False ∧ (p2 ∨ p5)) → ((((p2 ∧ False) ∨ (p5 → p1)) ∨ p1) → p5)) → (p4 ∧ (p5 ∧ (p4 ∧ (p1 ∨ False)))))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175270209819227796922783043399 : ((p2 ∨ (p4 ∧ ((p3 ∨ p5) ∨ ((False ∧ (p4 ∧ (p3 ∧ (p5 ∨ p1)))) → p3)))) → (((((p1 → (False ∨ p4)) ∨ p3) → p3) ∧ False) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
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
theorem thm_5_vars_150817629589048746051340249469 : ((((False ∧ ((True → ((True ∧ (True ∨ (p4 → p3))) → (True ∨ p4))) ∨ (p5 → p5))) → (p4 → p3)) ∨ p1) → ((p3 ∧ False) ∨ (True ∨ True))) := by
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
theorem thm_5_vars_341675133183658977065121457646 : (p2 → ((((p3 → True) ∧ (((p1 → (((p3 → p1) ∨ False) → False)) → (((p5 → (p2 ∧ False)) → False) → p4)) ∨ p3)) ∨ p5) ∨ (p2 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167015851098473234997353632487 : (((p3 → (True → (p3 ∧ (((p3 ∧ p5) ∧ (p3 ∧ ((p3 ∨ True) ∨ p2))) → p1)))) ∧ p5) → (((p3 ∨ (p4 → (False ∨ False))) ∨ p3) ∨ p5)) := by
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
theorem thm_5_vars_117106832295404474659118383485 : (((p2 → p3) → (False ∨ ((p1 ∨ (p3 ∨ ((p3 ∧ ((p5 ∨ False) ∧ (((p2 ∨ (p5 ∨ p2)) → p1) → p4))) ∨ True))) → p2))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



