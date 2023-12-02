variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136582447414240584299192692927 : (((p2 ∧ (p1 ∨ p3)) ∨ (p5 ∨ (((p4 ∧ (((p3 ∧ ((p5 → p3) ∨ p1)) → False) → (True ∨ p2))) → True) → p2))) ∨ (False → (True ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165134288898609360054960681947 : ((((False ∨ (((p4 → ((True ∨ (p3 ∧ p5)) ∨ True)) → p5) ∧ p4)) ∨ True) ∧ (False → p3)) ∨ (((p4 → (p1 ∨ p4)) → (p5 → p3)) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588487418154462997815043453509 : ((((((False → p2) ∧ (p5 ∨ (p4 ∧ (p2 ∧ (p2 ∧ (((((p5 ∧ p1) → (p4 → False)) ∧ False) ∨ (p2 ∨ p4)) ∧ p5)))))) ∨ p4) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119512891425642029781051476328 : ((p5 → (((p3 → False) → ((p4 ∧ ((((((True ∨ p2) ∧ p2) ∧ (p2 → p2)) ∧ False) → (p3 ∨ True)) → p3)) ∨ p3)) ∧ False)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343473883184863614648207672209 : (p2 → ((p2 → p3) ∨ (((((((True ∨ (p3 → p2)) → (p1 → p4)) → p1) → p4) ∧ (((False ∧ p5) → (p1 ∨ p3)) ∧ p3)) → p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119859151148183175042406559393 : ((((((((((False ∨ ((p2 → (True ∧ (p5 ∧ p1))) → p5)) → True) ∨ True) ∧ p2) → p2) → p1) → p2) ∧ (p4 ∨ p3)) ∧ p1) → (p4 → p2)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : ((((((False ∨ ((p2 → (True ∧ (p5 ∧ p1))) → p5)) → True) ∨ True) ∧ p2) → p2) → p1) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h8
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h12 : ((((((False ∨ ((p2 → (True ∧ (p5 ∧ p1))) → p5)) → True) ∨ True) ∧ p2) → p2) → p1) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h14 := h5 h12
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113421120694848788702361517687 : (((((p1 ∨ True) ∧ (p1 ∧ ((p5 ∧ (p4 ∨ (((False ∨ (True ∧ p2)) ∧ (p2 ∧ p4)) ∧ p2))) ∨ p5))) ∧ p4) ∨ (p4 ∧ p4)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322515457289944444859484028444 : (p5 ∨ ((p1 ∧ ((((False → p2) → p5) ∧ (((False → p1) → True) ∨ (p1 ∧ (((p4 ∨ (False ∨ (p3 → p3))) ∧ p4) → True)))) ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245181587049797627773794770478 : ((p2 ∧ False) ∨ ((((p4 → True) → p5) ∨ (((p3 ∧ ((p5 ∨ False) ∧ p2)) ∧ p2) ∨ p5)) ∨ (((p2 ∨ (p5 → p2)) ∨ (False → p1)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606739488510942421829030797422 : (((((((p3 → p1) ∧ (((p5 ∨ ((((p2 ∨ p1) → (p2 → (p2 ∨ False))) ∨ p5) → p1)) → p4) ∨ p2)) ∨ (True ∨ p2)) ∧ p4) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_64509361888439354274341608683 : ((p1 ∨ ((p2 → (True ∧ (p5 ∨ (((False ∨ p2) → p4) ∨ ((p2 ∨ p5) ∧ p2))))) → (p1 ∨ ((p2 ∧ ((p1 ∨ p3) ∨ p2)) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304711651634462988263816229397 : (p1 ∨ (((p3 → ((p3 → (False → (p1 → (p2 ∨ p4)))) → ((True → (p4 ∧ (p2 ∧ p4))) → (p5 → p2)))) ∨ (True → p5)) ∨ (p5 ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198239171912951131345449957037 : ((True ∧ (True ∧ (False ∧ (p3 ∨ (False ∨ False))))) ∨ (((p3 ∧ p3) ∨ False) ∨ (p4 → ((p2 → p5) ∨ ((((p4 ∨ False) → p5) → p4) ∧ True))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608134693337435280657717374858 : (((((((((p2 → p2) ∨ True) ∧ (p5 ∧ (p1 ∨ p1))) ∧ (p4 ∨ ((False ∨ (p5 → (p5 ∨ p4))) → (p3 ∧ p5)))) ∧ p3) ∨ p3) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_136396888072502836437651988132 : (((False ∨ ((p5 ∧ p2) ∨ p5)) ∨ (p1 → ((False ∨ (p3 ∨ p5)) ∨ (((p5 → p4) → (p1 ∨ (p2 ∨ p4))) ∨ p1)))) ∨ ((False → p4) → p3)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191127530665072835784792185764 : (((p3 → (False ∨ False)) ∧ (p4 → (p5 ∧ (p2 → p2)))) ∨ ((((p2 ∧ ((p2 ∧ (False ∧ p2)) ∨ p2)) ∧ ((p1 → p4) ∧ True)) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592660980188547486145001824591 : (((((p1 → (False ∨ (p5 ∧ ((False ∨ ((p1 → (((p4 → False) → (False ∧ p5)) → p3)) ∧ (True ∨ p1))) ∧ p3)))) → (False ∨ p3)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216884209132358825617964283166 : (((p2 ∨ (p5 ∧ True)) ∧ p3) → (((((p4 ∨ False) ∧ ((False ∧ p5) ∧ p5)) ∨ False) ∧ p1) ∨ (p5 → (p2 ∨ (((p1 → p3) → False) ∨ True))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140371916512214211750661068431 : ((((p3 ∨ (True → p1)) → (p1 ∨ (((p1 → False) ∨ (p3 → (p1 ∧ p2))) ∧ (p3 → True)))) ∨ ((p1 ∨ p4) → p4)) → ((p2 ∨ True) ∨ True)) := by
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
theorem thm_5_vars_127731550726317834881763967781 : ((True → (((p3 ∨ p3) → (True → ((p2 ∧ (p4 ∧ ((((p1 ∧ ((p3 ∧ True) ∧ True)) ∧ p1) ∧ p2) ∨ p3))) ∨ p4))) ∧ False)) → (p2 ∨ p5)) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689214770670539211979578195435 : ((((((True ∧ p5) ∧ ((p1 ∧ p1) ∨ (p2 ∨ (p3 → (True ∧ (p5 → p1)))))) → p2) ∨ (True ∨ (((True ∧ (True → p5)) → False) ∨ True))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_677742624232634128079186889201 : (((((p1 ∧ (((((False → p4) → (p3 ∨ False)) → False) → (p5 → p2)) ∧ (p2 ∨ (p3 ∧ True)))) → p5) ∨ ((False ∧ p5) ∧ (p3 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39268717627924501219972935592 : (((False ∧ (p3 ∨ ((((p3 ∨ (((p1 ∧ ((True → p3) ∧ p1)) ∧ False) ∨ p4)) → (True → (p5 ∧ p1))) ∨ p1) ∨ (p4 → p4)))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719462838128476596794847384184 : ((((p1 ∨ (p1 ∨ (p3 ∧ p5))) ∨ (((p1 ∧ ((p5 → p2) ∧ True)) → p5) ∨ (p2 ∨ ((p4 → (True ∨ (False → p1))) ∧ (p1 ∨ True))))) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134367307414937851245936067095 : (((p2 ∨ ((((((p2 ∨ p1) ∨ (p4 → ((True ∧ (p1 → p3)) ∧ p4))) ∨ p3) ∨ (p3 ∨ p1)) ∨ p4) ∧ p3)) ∨ True) ∨ (p3 ∧ (False ∨ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651488384299638573285089805929 : (((((True ∧ p3) ∧ (((p4 → (p1 → p1)) ∨ (p3 → (((p2 → False) ∨ (p2 ∧ p3)) ∨ (p4 ∨ (p1 → p3))))) → p3)) ∧ (p2 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137717201754788506520717722717 : ((p1 ∨ (((p5 ∨ p2) ∧ p5) → ((((p3 ∨ p3) → (True ∨ (p5 → False))) → p5) → (False ∨ ((p3 ∨ p5) ∨ False))))) ∨ ((p2 ∧ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117155428339398413954468277106 : ((True ∧ (((((False ∨ (p1 → (p5 ∧ p1))) ∧ ((p4 ∧ p3) ∨ (p3 → ((False ∨ p1) → (False → p4))))) ∧ p3) ∨ False) ∨ True)) ∨ (p5 ∧ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70295070264843690645310652898 : ((((p4 ∧ ((p4 → False) ∧ (p3 → ((p5 → ((p5 → p4) → (p3 → False))) ∧ (p3 ∨ (p5 → (p2 → False))))))) ∧ (p4 ∨ p3)) ∧ p4) → p1) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h10 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h11 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h12 := h8 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h14 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h15 := h8 h14
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218376210609228122515817166953 : (((p4 → p3) ∨ (p5 ∨ p3)) → ((((p1 → p3) → (p5 ∧ p3)) ∧ True) ∨ ((True ∨ p2) → ((p5 ∧ ((p4 ∧ False) → (p3 ∧ p2))) → True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253114901096612220558664767910 : ((True ∧ p5) → (((((((p2 → (p5 ∧ ((p4 ∨ ((p4 ∨ ((p4 ∨ p3) → p5)) → p5)) ∨ False))) ∨ p4) ∨ p4) → False) ∧ p2) ∨ True) ∨ p4)) := by
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
theorem thm_5_vars_665963286625143141992954734627 : (((((True ∧ (((((True ∧ p2) ∨ True) ∧ ((p5 ∧ p5) ∨ (((False ∨ p3) ∨ p1) ∨ p3))) ∧ p5) ∨ p2)) → p2) ∧ (p1 → (False ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307315134709406511996022327918 : (p1 ∨ (p3 ∨ (((((((p2 ∨ (p3 → (False ∧ ((False ∧ (p5 ∧ True)) ∧ (True ∨ p2))))) ∨ p4) ∧ p3) ∨ True) ∨ False) → False) → (p5 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((((p2 ∨ (p3 → (False ∧ ((False ∧ (p5 ∧ True)) ∧ (True ∨ p2))))) ∨ p4) ∧ p3) ∨ True) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679723230575846562080450051171 : (((((((((True ∨ (p1 ∧ (True ∧ p2))) ∧ p3) ∨ (p4 → p4)) ∨ (p4 → p4)) ∨ (False ∨ p1)) ∨ p3) → ((False → (p3 ∧ False)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198021819731410525836830771159 : (((p4 → p3) ∧ ((p2 ∨ p3) ∨ (p1 → False))) ∨ ((((p2 ∧ ((True ∧ (False ∧ p5)) ∨ p5)) ∨ (True ∨ (p2 → p5))) ∨ p3) ∨ (p3 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_337679937665558516027801936220 : (p1 → ((True → ((p3 ∧ (True → (p1 ∧ False))) ∨ (p5 ∨ (((p2 ∨ p2) → p3) → (False ∨ p4))))) ∨ (((p3 ∧ False) ∧ (True ∧ p5)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637574260369211652056392989005 : ((((((((p4 ∧ p4) ∧ p2) ∨ p5) ∨ ((p1 → True) ∧ p5)) ∨ (((p4 → ((True ∨ p3) ∧ False)) ∨ p4) ∨ ((p4 → p2) ∨ False))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155374284108443165814611296111 : (((p5 ∨ (p4 ∨ (True ∨ p3))) ∧ ((False → (False → p5)) ∨ (((p4 ∨ False) → p3) ∨ (p2 → p1)))) ∧ (((False ∨ p5) ∧ p2) ∨ (False → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44081549747055579478136342785 : (((((p2 → (p2 → False)) ∧ (True → (((p3 → (((p4 → p2) ∨ True) → (p5 ∨ p2))) ∧ p4) ∨ False))) ∧ (p4 → (False ∧ True))) → p1) ∨ p5) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158509918480986215897053191218 : (((False ∨ p4) → (p1 → (p2 ∧ (((p5 ∧ (((p5 → (p3 ∨ p3)) → p5) ∧ p1)) ∨ p5) ∧ p3)))) ∨ (False → (((p4 ∧ p1) → p3) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317125292217287449847287668024 : (p3 ∨ (p5 → ((False ∧ (p2 ∧ True)) ∨ ((p3 → ((True → p2) ∧ False)) → ((((p1 ∨ (p3 ∨ (False ∨ p3))) ∨ (p5 ∧ p1)) ∧ p5) ∨ True))))) := by
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
theorem thm_5_vars_179559573571689208736274181486 : ((p2 → (((p2 ∧ ((p1 ∧ (p2 ∧ p5)) → p3)) → (False ∧ p3)) ∨ p2)) ∨ ((p3 ∨ (p2 ∧ ((p4 ∨ (p5 ∨ (p3 ∧ p1))) ∨ p5))) → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309378925051607301122023458217 : (p2 ∨ (((p2 ∨ False) → ((True → (((p2 ∧ (((p2 → True) → p4) ∧ p1)) ∨ (p2 ∧ p5)) ∧ ((p4 ∧ p3) ∨ False))) ∨ False)) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137837232648768424209225562176 : ((p3 ∨ ((((p5 ∨ p4) ∨ (((p2 → p3) ∨ p2) → p3)) ∨ ((p3 ∧ p3) ∧ True)) → ((p2 ∧ p2) → (p4 ∧ p2)))) ∨ ((p5 → True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301160498884247771688038859044 : (False ∨ ((p1 ∨ (False ∧ ((p2 ∨ (p5 ∧ p3)) ∨ p4))) ∨ (((p2 ∨ (True ∨ ((p2 ∨ (p3 ∨ p1)) ∨ (p3 ∧ p3)))) ∨ (p2 → p3)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_55275703690693952000619288232 : (((True ∧ ((False ∨ (True ∧ p5)) ∧ False)) ∨ ((((p3 → ((p1 ∧ ((p5 ∧ False) ∧ p1)) ∧ p5)) → p3) → ((p5 → True) ∧ p4)) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62468447405309519799736336602 : ((p3 ∧ ((p4 ∧ p4) ∨ ((p3 ∨ True) ∧ (((p5 ∧ (True ∨ False)) ∧ ((((p2 ∧ p2) ∨ ((p1 ∧ False) ∧ p3)) → p1) → p2)) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810308670533269076907340105818 : (((p5 → (((((p5 ∨ p1) ∨ p5) ∨ (((p2 → False) ∨ p4) ∧ p4)) ∨ p2) → ((p4 → p3) ∨ (p5 → (((p2 ∧ p4) ∨ p5) ∨ p5))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h9
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h20
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184850036937550633984319460342 : (((p4 → ((p1 ∧ p2) ∨ p2)) → (p4 ∧ ((p2 ∧ False) ∧ p4))) ∨ (p5 ∨ ((p3 ∨ ((p4 ∧ (False ∧ False)) → (False ∨ p5))) ∨ (p4 ∧ p5)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218687858813272999880065984509 : ((True ∧ (p5 → (p4 ∨ p1))) → ((p5 → ((p5 ∧ p5) → (((False → False) ∧ (p4 ∨ p1)) ∨ (p3 ∨ p1)))) ∨ ((False ∧ p4) ∧ (p3 ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h8 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h8
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178285401942225008470058577978 : (((p2 ∧ (False ∧ (p2 ∧ ((p4 → p3) → (p4 ∨ p3))))) ∧ (p4 ∧ p1)) ∨ (((p1 → (p4 ∧ p5)) ∨ (p3 ∧ (p3 ∨ (False ∨ p5)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149386626442625199234041232949 : (((p4 → p5) → (((((p3 ∨ p3) → False) → True) ∧ (True → (p4 → p3))) ∧ (False ∨ ((p2 → p4) ∧ True)))) ∨ ((p5 ∨ (p5 → p5)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90223532577347423990544351679 : (((False ∨ (p2 ∨ True)) → ((p5 ∨ ((((False ∧ False) ∨ p3) ∧ p3) ∨ (p3 → p3))) → (((True ∨ False) ∧ p2) ∧ (True → (p5 ∧ p5))))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ (p2 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p5 ∨ ((((False ∧ False) ∨ p3) ∧ p3) ∨ (p3 → p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209507228501240419446405920953 : ((p4 → ((p2 ∨ (p5 → p5)) ∧ p3)) → (((p3 → p2) ∨ ((p1 → (True → (p2 ∨ p3))) ∨ (False ∨ True))) ∨ (False → (p4 ∧ (False → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_260408777696902929493644854850 : ((p3 → True) → ((((p5 → ((True → (((False ∨ p1) ∧ p1) ∨ (True → p5))) ∨ ((False → (p5 ∨ True)) ∧ p3))) ∨ (p5 ∨ p5)) → False) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p5 → ((True → (((False ∨ p1) ∧ p1) ∨ (True → p5))) ∨ ((False → (p5 ∨ True)) ∧ p3))) ∨ (p5 ∨ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h3
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230738754002348475634742756737 : (((p5 → p2) ∧ p4) → ((False ∨ ((p4 ∨ True) → ((((p2 → p1) → p5) ∨ False) → False))) ∨ (p3 → ((p4 → (p4 ∨ p1)) ∨ (p3 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171715028886308466373074535730 : (((((((((p5 ∧ True) ∧ False) ∨ p3) ∧ (True → p2)) → p3) ∨ p1) ∧ p1) → p2) ∨ (True ∧ ((p3 ∨ ((p5 ∧ p4) ∨ True)) ∧ (True ∨ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219630335931821862197526912441 : ((False → ((p1 ∨ p2) ∨ p5)) → ((True ∧ (p1 ∨ ((True ∧ p4) ∨ ((((p4 ∧ False) ∨ p4) ∨ (True ∧ p5)) ∧ p5)))) ∨ (p2 → (p5 → p2)))) := by
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
theorem thm_5_vars_330860115061677943490075225724 : (True → (p3 → ((((((((((p3 ∨ p1) → p2) ∨ p2) ∧ p1) ∨ (False ∨ p3)) ∨ p1) → False) ∨ p3) ∨ p5) ∨ ((False ∨ (p3 ∨ p2)) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669549547624488039408445048307 : (((((p3 → (p4 → ((p5 ∧ (p1 ∨ ((p2 ∨ p5) ∨ (p3 ∨ True)))) ∧ ((False ∨ True) ∧ p3)))) → (True ∧ p3)) ∨ (False ∧ (p1 ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200677711233832398457107632355 : ((p1 ∧ (True → (True → (p3 → (p3 ∧ True))))) → ((p2 ∧ (False ∨ (p3 ∨ (((False ∧ p5) ∧ (p3 → p4)) ∧ (p1 → (False ∨ p3)))))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616067814903978532056959988067 : (((((p3 ∨ (((((p4 ∨ p4) ∧ True) ∧ p5) → (p1 ∨ p4)) ∨ (p3 ∨ p5))) → ((p5 ∧ p4) ∨ ((p4 ∧ False) → (p3 ∨ p5)))) ∨ p3) ∨ p2) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- False on the left can always be used.
        apply False.elim h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135725718781353622791888833569 : ((((p5 ∧ ((False ∨ (p3 ∨ p3)) ∧ (p5 → ((True → p3) ∨ False)))) ∧ p4) ∨ (False → (False → ((True ∧ True) → p2)))) ∨ ((p2 ∧ p5) ∧ p5)) := by
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42709488685734340852027872044 : (((p5 ∨ ((p5 ∨ p5) ∨ (((p5 ∨ ((p1 ∨ (False → False)) ∧ (p5 ∧ False))) → p4) → (p2 ∧ ((p4 ∨ (False ∧ False)) ∧ p4))))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41102621942704360163319164243 : (((((p4 → ((p1 → (p4 ∧ p5)) ∧ p2)) ∧ (p4 → ((p3 → (p1 → p4)) ∧ (p2 → (p3 ∨ False))))) ∧ ((p5 → p4) ∨ p5)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183779299370047513952932339759 : (((((p2 → (p5 ∨ True)) ∨ (p2 → (True ∨ p1))) ∧ p1) ∧ False) ∨ (p4 ∨ (p1 ∨ (((p4 → p1) → p1) → (True ∨ (p4 → (p2 ∧ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_60791041979925421174281741428 : ((True ∧ (True ∧ ((p3 → p2) → ((p5 → ((p1 → (p1 → (p5 → (p1 ∧ True)))) ∧ (True ∧ (False ∧ True)))) → (False ∨ (False ∨ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56474327049854377478824510464 : ((((True → p5) → (p1 ∧ True)) → (p5 → ((((True → p3) → True) ∨ p5) → ((p2 ∧ (p2 ∧ (False ∧ p3))) ∨ (p4 → (p1 ∨ p2)))))) ∨ p4) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : (True → p5) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h6
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h12 : (True → p5) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h14 := h1 h12
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199364742282811900658264854761 : ((((p4 ∨ (False → p5)) ∧ (False ∨ p1)) ∨ p3) → ((((p2 → (p1 ∧ p3)) ∨ True) ∨ (False ∨ ((((False ∨ True) → p2) ∧ True) ∨ p5))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304021787144203417286588896921 : (p1 ∨ ((False ∧ (p4 ∨ ((((p1 ∨ ((p5 → p5) ∧ p1)) ∧ (False → (p1 ∧ (p5 → p1)))) ∨ False) ∨ (((False → True) → p4) ∨ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325732454398377127600894570920 : (p5 ∨ (p2 ∨ ((((p3 ∨ (((((True → p2) ∨ True) ∨ (False ∧ (False ∨ True))) ∨ (p4 ∧ (p2 ∨ p2))) ∨ (p3 → p3))) ∧ False) ∨ True) ∨ p2))) := by
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
theorem thm_5_vars_174388532280679865247259886198 : ((((True ∨ p2) ∨ ((p1 → (p2 ∧ p5)) ∧ False)) ∧ ((p1 ∨ (p1 → p1)) ∨ p2)) → ((((p2 ∨ (False → p4)) ∨ p3) ∧ p3) → (p1 ∨ p3))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h1.left
      let h8 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h11 =>
            -- Disjunctions on the left can always be decomposed.
            cases h11
            case inl h12 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h12
            case inr h13 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h4
          case inr h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h4
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h16 =>
            -- Disjunctions on the left can always be decomposed.
            cases h16
            case inl h17 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h17
            case inr h18 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h4
          case inr h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h4
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- False on the left can always be used.
        apply False.elim h22
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h1.left
      let h25 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h26 =>
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h28 =>
            -- Disjunctions on the left can always be decomposed.
            cases h28
            case inl h29 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h29
            case inr h30 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h4
          case inr h31 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h4
        case inr h32 =>
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h33 =>
            -- Disjunctions on the left can always be decomposed.
            cases h33
            case inl h34 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h34
            case inr h35 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h4
          case inr h36 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h4
      case inr h37 =>
        -- Conjunctions on the left can always be decomposed.
        let h38 := h37.left
        let h39 := h37.right
        -- False on the left can always be used.
        apply False.elim h39
  case inr h40 =>
    -- Conjunctions on the left can always be decomposed.
    let h41 := h1.left
    let h42 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h41
    case inl h43 =>
      -- Disjunctions on the left can always be decomposed.
      cases h43
      case inl h44 =>
        -- Disjunctions on the left can always be decomposed.
        cases h42
        case inl h45 =>
          -- Disjunctions on the left can always be decomposed.
          cases h45
          case inl h46 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h46
          case inr h47 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h4
        case inr h48 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h49 =>
        -- Disjunctions on the left can always be decomposed.
        cases h42
        case inl h50 =>
          -- Disjunctions on the left can always be decomposed.
          cases h50
          case inl h51 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h51
          case inr h52 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h4
        case inr h53 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
    case inr h54 =>
      -- Conjunctions on the left can always be decomposed.
      let h55 := h54.left
      let h56 := h54.right
      -- False on the left can always be used.
      apply False.elim h56



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98816368211796929227667645489 : ((True → ((((p4 → p5) ∧ p1) ∧ ((p1 ∧ ((((p3 ∧ (True ∧ p3)) ∧ (False ∧ p2)) ∨ (p5 ∧ p4)) ∨ (p5 ∨ p5))) → True)) ∧ False)) → p4) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50541207666325444373566708538 : (((((((p5 → p4) ∨ p2) → ((p3 → (p3 ∨ p5)) ∨ True)) → ((False ∧ (p2 ∨ p2)) ∨ p4)) ∨ p2) → (((p3 ∨ False) ∨ p1) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768761297730904626038887807972 : (((p5 ∧ ((((False ∧ p4) ∨ p3) ∧ (p2 → (p4 ∧ True))) ∨ (p2 ∨ (((p3 ∨ False) → (p5 ∨ ((p4 ∧ (p4 ∧ p5)) ∨ False))) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810095134716135670479351289953 : (((p5 → (((False ∨ ((((True → p1) ∧ p2) → (p4 → (p5 ∧ p2))) ∧ (p4 ∧ (p3 → p3)))) ∨ True) → (((False ∨ p2) → p4) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299133135236973545310445664535 : (False ∨ ((((((p1 ∧ p4) → (p1 ∨ True)) → ((p3 → p5) ∧ (False ∧ (p3 → (((p4 → True) ∧ p4) → p1))))) ∨ (True ∨ p4)) ∨ p4) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_509548215175343030834666288 : ((((p5 ∧ ((p4 → p3) ∨ False)) ∨ (p4 ∨ ((p1 ∧ (p1 ∨ ((p4 ∧ True) ∧ ((p4 → (True ∨ p3)) ∧ p3)))) ∨ p1))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344129751696385016753000404943 : (p2 → (False ∨ (((True ∧ (True ∨ (p4 ∧ p4))) → (False ∨ p3)) → ((p2 → (p1 → (((p1 ∧ p3) ∨ (False → p3)) → (p3 ∨ False)))) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : (True ∧ (True ∨ (p4 ∧ p4))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206988872675399961309177712053 : ((((False ∨ p5) ∧ (p1 → p2)) ∧ p2) → (((p1 → (p3 ∨ (p2 ∧ p4))) → (p5 → p4)) ∨ ((True → (p2 → ((False → p5) → p4))) → p5))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171686240868954482034491344443 : (((p4 ∨ ((p1 → (p3 ∨ (p2 → ((p4 ∧ (False → p2)) ∨ p3)))) → p1)) ∨ True) ∨ ((True ∧ (p4 ∧ ((True ∧ False) ∧ (True ∨ p4)))) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47062817946839464985397684397 : ((((((p3 ∧ p5) ∧ (True ∧ ((False ∨ ((p2 ∨ p3) ∨ p4)) ∨ True))) → (((p2 → p4) ∧ p5) ∧ p2)) ∨ (p3 ∧ p3)) ∨ (p5 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261869016826784913298596673851 : (True ∧ (((((True ∧ p2) ∨ ((p4 → True) ∧ (((p1 → True) ∧ p3) ∧ p1))) ∧ False) ∨ ((p5 ∨ ((p4 → False) ∨ (p1 → p3))) ∨ True)) ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213516003086997969952305258678 : (((p4 → (True → p1)) ∧ False) ∨ (((p4 ∧ (((((True ∧ p4) ∨ p1) ∨ p2) ∨ p2) → (p1 → False))) ∧ p2) ∨ ((p4 ∧ True) ∨ (False → p4)))) := by
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
theorem thm_5_vars_39766459778873948790820513846 : (((True → (((p4 → (False ∧ p3)) → (True ∨ (p1 ∨ p2))) ∧ (((p5 → (p4 ∧ p4)) → (((p3 ∨ p2) ∧ False) ∧ p1)) ∨ False))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153095529986839482920298104712 : ((p3 ∧ (p4 → ((p2 ∧ ((((p2 → (p3 ∨ (False ∧ p5))) → True) ∨ False) → (p3 ∧ (p4 ∧ True)))) ∧ False))) → ((p3 → p4) ∨ (True → True))) := by
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
theorem thm_5_vars_737487879410688411077054045021 : ((((p5 → True) ∧ ((((((p1 ∧ p5) ∧ p5) ∨ (p5 ∨ (p2 → (p4 ∧ ((p5 ∨ p4) ∨ p2))))) ∧ p2) ∨ (p2 ∧ p4)) ∨ (p3 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140184840951132394504910540162 : ((((((p3 ∧ (True → p1)) ∨ (p2 → True)) ∨ p2) ∨ (p1 ∧ (((p3 ∨ p3) → (p1 ∧ False)) → p4))) → (p2 ∧ p5)) → ((p4 ∨ p2) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p3 ∧ (True → p1)) ∨ (p2 → True)) ∨ p2) ∨ (p1 ∧ (((p3 ∨ p3) → (p1 ∧ False)) → p4))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306487551381402369907235030938 : (p1 ∨ ((p2 → False) ∨ ((p4 ∨ False) ∨ ((p4 → (((p2 ∧ p5) ∨ p5) ∧ False)) ∨ (((p5 ∨ p4) → (p4 → False)) → ((p2 → p2) ∨ p3)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51927484238496543731471761270 : (((((p3 ∨ ((p3 ∧ (p2 ∧ p5)) ∧ p2)) ∨ (p5 ∧ p4)) ∨ ((p1 ∧ p3) ∨ p2)) ∨ ((((p5 ∨ True) ∧ (p1 → p1)) ∧ True) → True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314213010665256110593036663429 : (p3 ∨ ((p4 ∨ ((p1 → (((p5 → p4) ∨ (p1 → (True ∧ (((p5 ∧ (p3 ∧ p5)) ∨ False) ∧ False)))) ∨ p5)) ∨ True)) ∧ ((False → p3) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259605899883971096127038408321 : ((p1 → True) → (p4 → (p2 ∨ (((((p3 ∧ p4) ∨ False) ∧ False) ∧ (p3 ∧ (((False ∨ (p2 → True)) ∨ p2) ∨ ((False ∧ p2) ∨ True)))) ∨ True)))) := by
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
theorem thm_5_vars_45806146662991288247916027058 : (((p1 → (p1 ∧ (True ∧ ((p3 ∨ (p3 ∨ ((p5 ∨ True) ∨ False))) ∨ (False ∧ (p3 ∧ (p4 ∨ (p3 ∧ ((p2 ∧ p2) ∨ p1))))))))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41216650164348584609254513201 : ((((((((((True ∨ (p2 ∨ p1)) → True) ∧ (True ∨ p2)) ∨ p4) ∨ (False ∧ p2)) ∧ p5) → p5) ∧ (((p5 ∧ p1) → p4) → p5)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157170041318138100706647043300 : (((((p1 → (p3 → (p1 → ((((False → (p1 → p1)) → False) ∨ p3) ∨ p1)))) ∨ p5) → p3) → p1) ∨ (p3 → (((True ∧ False) → p5) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117066118225685332569585806653 : (((p5 ∨ p5) → (p3 → (p2 ∧ (((((p5 ∧ p3) ∨ p4) ∧ (p1 ∨ (p1 ∨ p4))) ∨ (False ∧ (p1 ∨ True))) ∨ (p3 → False))))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205863296135119748608907574946 : (((p5 → p1) → ((p4 → p4) ∧ p4)) ∨ (p5 ∨ (((((((True → p5) ∨ (p2 ∧ p1)) ∨ False) ∧ p2) ∧ p1) ∨ (True → True)) ∨ (False ∧ p4)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704334802173113366982780306659 : (((((p1 → ((p3 ∧ False) → p3)) ∨ (True → (p2 ∨ p5))) → ((((p5 ∧ True) → (((p2 ∨ p4) ∧ True) ∧ True)) ∧ (p1 ∨ p3)) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784717212126789663613009172908 : (((p3 ∨ (p4 ∨ (p5 → (((p5 → p3) → (p4 ∧ (((p2 → p4) ∨ True) ∧ (p5 ∧ (p4 → ((p5 → p1) ∨ True)))))) ∨ (False → True))))) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774093527662939436477731061555 : (((False ∨ ((p3 ∧ (p5 ∧ (p3 → (((False → p5) → ((False ∧ ((p1 ∨ ((False ∨ True) ∧ p5)) ∨ p2)) ∧ True)) ∧ False)))) ∨ (False → True))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



