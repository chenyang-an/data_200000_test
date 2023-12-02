variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634357559069441888403309438383 : (((((((((True ∨ (p3 ∨ (False → (p3 ∧ p2)))) ∧ ((p2 → (True ∨ False)) → True)) ∧ False) → p4) ∧ p1) ∧ (p4 ∨ (False → p2))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157453860002190308140599187775 : ((((((((p5 ∧ (p2 ∧ True)) ∨ (p3 → p3)) → False) ∨ (p4 ∧ p1)) → p5) ∧ p5) ∨ (True ∧ True)) ∨ (((p5 → p4) → False) ∨ (p1 ∨ False))) := by
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
theorem thm_5_vars_227758428924518034299256765650 : ((p1 ∧ (p4 ∨ p4)) ∨ ((p4 → (True → (False ∧ (((p3 ∨ p5) ∨ p3) ∨ (p1 ∨ (p2 ∧ ((p3 ∧ p3) ∨ p5))))))) ∨ (p1 → (True ∨ True)))) := by
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
theorem thm_5_vars_121881227816656577478480332858 : (((True ∧ (p4 ∨ ((((p1 → False) ∨ p3) ∨ False) ∨ (p1 ∧ (p3 ∨ ((False → p1) ∨ ((p3 ∧ (True ∨ p1)) ∨ p4))))))) → p5) → (p1 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (True ∧ (p4 ∨ ((((p1 → False) ∨ p3) ∨ False) ∨ (p1 ∧ (p3 ∨ ((False → p1) ∨ ((p3 ∧ (True ∨ p1)) ∨ p4))))))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163660361858291183839274363434 : (((p3 ∨ True) ∨ ((p5 ∧ ((((p4 → p1) ∧ (False → p4)) ∨ (False ∨ p4)) ∧ False)) ∨ p1)) ∧ ((False ∨ ((p5 → p4) ∧ p2)) ∨ (p4 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_313663588466699167551421830119 : (p3 ∨ (((p5 ∧ False) ∨ ((p3 → ((p3 → (True ∨ p1)) ∧ (p1 ∨ (((p1 ∧ False) ∧ ((p3 → p2) ∨ p5)) ∨ (p5 → p3))))) → False)) → p2)) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (p3 → ((p3 → (True ∨ p1)) ∧ (p1 ∨ (((p1 ∧ False) ∧ ((p3 → p2) ∨ p5)) ∨ (p5 → p3))))) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h6
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158504123050471627599449262719 : (((True ∨ False) → ((p2 ∨ p5) → (p3 ∨ ((False → False) ∧ ((p2 → p1) ∧ ((p4 → p1) → p2)))))) ∨ (False → ((False ∨ p5) → (p4 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169068255407996530593520548395 : ((p3 → (((False ∨ (p5 ∨ (True ∨ False))) ∧ p2) ∧ ((False ∧ ((p3 → False) ∧ p4)) → p1))) → ((p1 → p2) → ((p2 ∧ (False → False)) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_390010160459740501342078048296 : (((((((p4 → p3) ∧ (((p5 → p4) → p2) → p1)) ∧ p4) ∧ (p2 → ((True ∧ ((p4 ∨ p3) ∧ False)) ∧ ((False ∨ p4) ∨ False)))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_42487683864578700064167161689 : (((False ∨ ((((p4 ∨ p2) → (False → (p1 → True))) ∧ (((p2 → p1) ∧ ((p5 → (False ∨ (p5 ∧ p2))) ∨ True)) → p3)) ∧ True)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41682502591855423735688211842 : ((((p2 ∧ (p3 ∨ ((p2 → p4) → p1))) ∨ ((p2 → ((False → (p2 ∧ p5)) ∧ p4)) ∧ (((True ∧ p1) ∧ p5) ∨ (p1 → False)))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52670825268802296115637751506 : (((False ∨ ((((p5 ∧ p1) ∨ (p1 ∨ (p5 ∨ p1))) → (p5 ∧ False)) ∨ p1)) ∨ (((True ∨ (True ∨ p4)) ∧ (p5 ∨ (False ∨ False))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184851834438683532121804833609 : ((((False ∧ False) ∧ p1) ∧ (p1 ∧ (p4 ∧ ((p4 ∧ False) → p4)))) ∨ (True ∧ ((((p4 ∨ True) ∧ (p4 ∨ p1)) → True) ∨ (p2 → (p1 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358606911649961469503519874304 : (p5 → (p3 → ((False → (((p1 ∨ p4) → p2) → p3)) ∧ ((((True → ((p3 ∨ p5) ∨ (p5 ∧ p2))) → p4) ∧ (False → (False ∧ False))) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225905022094628434388194676284 : (((p1 ∧ p4) ∨ False) ∨ (((p2 ∧ False) ∨ (True ∧ (((p4 ∨ False) → (p3 ∨ (((p5 ∧ False) → False) ∧ (True → (p4 → p3))))) ∧ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768321714698157537327587474101 : (((p5 ∧ ((p3 → ((((p4 ∨ (True → p4)) ∧ p4) ∨ False) ∨ (p1 ∧ (False ∨ ((p4 → p3) ∧ (p1 → p2)))))) ∨ ((p3 ∨ p3) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46867550629198428943604410501 : ((((p3 ∨ (p3 → (((((p1 ∨ False) ∨ ((False ∨ False) ∨ p5)) → ((p4 ∨ p5) → p4)) ∧ True) ∧ (p4 ∨ p1)))) ∧ p1) ∨ (p1 → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115004005544983333091219942420 : (((((p4 → p1) ∧ p4) ∧ ((p5 ∧ True) ∧ (True ∧ (p3 → p3)))) ∧ (p5 ∧ ((p2 ∧ (p4 ∧ True)) ∨ (False ∨ (p3 ∨ p3))))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199614267998279119516254170146 : ((((p2 → ((p1 → p3) → p4)) → p5) → p3) → (((((p3 ∧ (False ∧ p4)) ∨ (p3 ∨ p2)) → (False ∨ (p1 → p2))) ∧ True) ∨ (p4 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60409497524334906368348213804 : (((p4 → False) → (((((p4 → (((p1 ∨ p5) → p4) → p4)) ∧ p5) ∧ p4) ∧ p2) ∧ (p4 ∧ ((p1 ∧ ((p4 → False) → p5)) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62201818809401153826640411603 : ((p3 ∧ (((p4 ∨ ((p3 ∨ (p5 ∧ p3)) → p2)) ∧ (False ∧ (False ∨ (False ∧ (p2 ∨ (((False ∧ (p2 → p3)) ∨ True) ∨ p2)))))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_469730621765650645309044643256 : ((((True → ((((p2 ∧ p2) → p3) → (False → (p4 ∧ p2))) ∨ (False ∨ p3))) → ((p2 → ((p1 → False) ∨ ((p1 ∨ p3) → p2))) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112889285286493677014050355104 : ((((p2 ∨ True) ∧ (p4 ∧ ((p2 → p2) ∨ (p1 → (((p5 ∧ ((p1 ∨ p4) ∧ False)) ∨ (p5 ∨ p1)) ∨ (p4 ∧ False)))))) → False) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68421193549440231135294545212 : ((p3 → ((False ∨ False) ∨ (((p5 ∨ (p3 ∨ p2)) ∧ ((p2 → (p4 ∨ (p3 ∧ (p5 ∧ (p3 ∨ p5))))) ∨ ((False ∧ p5) ∨ p5))) ∨ p3))) ∨ p3) := by
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
theorem thm_5_vars_112166181428724944100945056061 : (((p3 ∧ ((p4 ∨ (p4 ∧ ((True ∨ (((True ∧ False) ∨ False) ∧ (p1 ∧ (False → p3)))) → p4))) → (p2 ∨ (p4 → p5)))) ∨ True) ∨ (p4 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341663278664979467349329177585 : (p2 → (((((p1 ∨ p4) ∨ (False ∨ p4)) → ((((True ∧ (True ∨ p5)) ∨ p4) ∧ p1) ∨ (p1 ∨ (p1 ∧ (p1 ∨ p5))))) ∧ True) ∨ (p1 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157274930321773060428638693433 : (((((True ∨ p4) ∨ p4) → (((((True ∧ (p5 ∨ p5)) ∧ (p3 → False)) → False) ∧ p3) ∨ True)) → p2) ∨ (p1 → ((p5 → p5) ∨ (p5 ∧ p4)))) := by
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
theorem thm_5_vars_196779521886556616921036632828 : ((((p5 ∧ p1) ∧ (p3 ∧ (p3 ∨ p5))) ∧ p5) ∨ (p4 → ((False ∨ True) ∨ (p1 ∨ (((p3 ∧ (((p1 ∨ p4) ∨ p4) ∨ p4)) ∨ p4) ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621076840167223648900006023926 : (((((p2 → p4) → (((p1 ∨ False) → (False ∨ (p5 → p1))) → ((True ∧ (p4 ∨ p2)) → (p3 → (p2 ∧ ((p5 ∨ False) ∧ p4)))))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112207603096510274861096384066 : (((False ∨ ((p3 ∧ ((((False → (False ∧ (p5 → (p5 ∨ (True ∨ ((False ∧ True) ∨ p4)))))) ∧ p3) ∨ p1) ∧ False)) ∨ p2)) ∨ True) ∨ (p1 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324674627150349102139713872668 : (p5 ∨ ((p4 ∧ (p1 → p2)) ∨ (((p3 ∨ ((((p2 ∨ p2) ∨ p1) → p4) ∧ p4)) ∨ (True → (p2 ∧ p2))) → (p1 ∨ (p4 ∨ (False → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318902566533970082672996101668 : (p4 ∨ ((p4 ∨ ((p4 ∨ (p3 ∧ p5)) ∨ (((p2 → p4) ∨ (((p2 → ((True → p3) → p5)) ∧ p3) ∨ p4)) → True))) ∨ (True ∨ (False ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354614772869698031972465647456 : (p5 → ((((((p3 ∨ (True → (p4 ∧ p4))) ∨ p2) → ((False ∨ False) ∧ (False → True))) ∨ ((p5 ∧ p1) ∧ ((True ∧ p2) → True))) ∨ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319934476923296436054389232115 : (p4 ∨ ((p3 ∨ ((p5 ∨ p3) ∧ p5)) → ((p3 ∧ p3) ∨ ((((p2 ∧ (p4 → p1)) ∨ ((p3 → False) ∨ p5)) ∨ (False → (p1 → p4))) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257328974124198714748711831822 : ((p2 ∨ p4) → ((p4 ∨ (((True → (p1 → True)) ∧ True) → (False ∧ (p5 ∧ p1)))) ∨ (p2 ∨ (((p3 ∨ (p5 → p5)) → p1) → (True ∧ p5))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763811691507008438022211637091 : (((p3 ∧ (p3 ∨ ((p2 ∨ (((True → (p2 → (p2 ∨ True))) ∧ (True → (True ∧ (p3 ∧ ((p5 → (False ∧ p2)) ∨ False))))) ∧ p2)) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226453953814253627395483584510 : (((p1 → p3) ∨ p4) ∨ (((((p3 ∧ (p4 → False)) ∧ False) → p4) → (p2 ∨ p5)) ∨ ((True ∨ (((p2 ∧ (p4 ∨ p3)) ∨ False) → p2)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39598528331470001228048286601 : (((p2 ∨ (((p1 ∨ p5) ∨ ((True → p2) → ((p2 ∧ (((((True → False) → p3) ∧ (False ∨ p4)) ∧ p3) → p5)) → True))) → p3)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641248165345449041994294063369 : (((((p5 ∨ False) ∨ ((p2 → (((p3 ∧ ((p1 → True) ∨ p4)) ∨ p2) ∧ (p1 ∨ ((p4 → ((p5 ∨ p2) ∧ p4)) ∨ False)))) ∨ p1)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53346133601489902101587738200 : ((((False ∨ (False → (p4 → ((p3 → (False ∨ p4)) ∧ p3)))) ∧ p1) → ((p2 → (p2 ∧ p4)) ∨ (p3 ∨ (True → (p3 → (p5 ∨ True)))))) ∨ p1) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200154089199773865477949435835 : ((((p2 ∧ p1) ∨ p2) ∨ (p2 ∧ (True → False))) → (p1 → ((p5 ∨ False) ∨ ((p4 ∧ (p2 → p1)) → (p5 → ((p1 ∧ p2) ∧ (p1 → p5))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h6
      -- Conjunctions on the left can always be decomposed.
      let h11 := h7.left
      let h12 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h5
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the left can always be decomposed.
      let h14 := h7.left
      let h15 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h19 := h17.left
      let h20 := h17.right
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Conjunctions on the left can always be decomposed.
      let h21 := h17.left
      let h22 := h17.right
      -- One of the premise coincides with the conclusion.
      exact h16
      -- Implications on the right can always be decomposed.
      intro h23
      -- Conjunctions on the left can always be decomposed.
      let h24 := h17.left
      let h25 := h17.right
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h26.left
    let h28 := h26.right
    -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
    have h29 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h28, we can now drive its conclusion.
    let h30 := h28 h29
    -- False on the left can always be used.
    apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622044113147698840159916077807 : ((((p2 ∧ (((p4 ∧ (p3 → (p4 ∧ ((p3 ∨ p4) ∧ ((p3 ∧ ((p1 → (True → (p2 ∧ p1))) → p2)) ∨ True))))) → False) → False)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_774521523181795385666860504811 : (((False ∨ (((p5 ∧ ((False → False) → False)) ∨ (((p3 ∨ (p4 ∧ p1)) → p3) → p1)) ∨ ((p4 ∧ (p5 → p5)) → ((p4 ∨ p3) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43376247561299108041796741706 : ((((((((p3 ∨ True) → ((p5 ∧ True) → (True ∧ True))) ∧ (((p5 → p5) ∧ p1) ∨ p2)) ∧ p2) ∨ (False ∨ (p1 → False))) ∨ p1) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192406521019942065607942228679 : (((((((p4 → p4) ∨ True) ∧ True) → p2) ∨ p5) ∨ p5) → ((p3 ∨ p4) ∨ (p4 → ((p4 ∨ ((p3 ∧ p5) ∧ p1)) ∨ ((p4 ∨ p3) ∧ p5))))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301688921556766146358064973612 : (False ∨ ((True ∨ True) ∧ ((((False ∨ ((p5 ∧ (False ∧ p5)) ∨ p1)) ∧ (p1 ∨ ((False ∧ ((False → p3) ∧ (p2 ∨ p1))) ∨ p2))) ∨ p1) ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322219711862287339397707114376 : (p5 ∨ ((((p2 ∨ (p4 ∧ (p5 → p4))) → ((p4 → False) ∨ (((p1 ∨ (p1 ∨ p5)) → (p2 → (p3 ∨ True))) ∧ (False ∨ p2)))) ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177853075842326255747163285996 : ((((((p2 → (p4 ∨ (p1 ∨ (True ∧ p1)))) ∨ p3) ∨ p2) ∨ p4) ∨ True) ∨ ((p3 ∨ p3) ∨ (p4 → ((p1 ∨ False) ∧ ((True → p4) ∧ False))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709074824356000727079716799321 : ((((((p4 ∨ p5) ∨ p1) ∨ (False ∧ (p3 ∧ p4))) → ((p3 ∧ False) ∨ ((p2 → (p5 ∧ (((p1 → (True → True)) → True) → True))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2130004325349507248119261254 : (((False ∧ p3) → (p4 ∧ (p5 ∨ (((p5 ∨ (True → (True ∧ False))) ∨ (p3 ∨ p3)) ∧ True)))) → ((p4 ∨ p4) ∨ (p4 → (False → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255667126682166461937712281679 : ((p5 ∧ p5) → ((((((p2 ∧ (p4 ∨ p4)) ∧ ((True → p5) → (((p3 ∨ p1) → p2) ∨ p1))) ∨ p5) ∨ False) ∨ ((p1 ∧ p5) ∨ p2)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46885789763153354616935921307 : ((((((((((True ∨ (p3 ∨ ((p1 ∧ p5) → (p5 ∧ p4)))) ∧ p3) → p5) → False) ∧ (p1 ∧ p2)) → p4) ∨ p3) ∨ True) ∨ (True ∧ p5)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148101882822221382535162481506 : ((((((((p5 ∨ (p1 → p4)) ∨ False) ∨ p1) → ((True → p5) → p3)) → p5) → (p4 → True)) → (p3 ∨ True)) ∨ (p1 ∨ (p5 ∧ (p3 → True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716647864210663742751856400092 : (((((p5 ∧ p5) → (p4 → p4)) ∧ ((p3 ∧ (((((p3 → ((p2 ∨ (p4 ∨ p1)) ∨ p4)) ∨ p4) → p3) → (p3 → p2)) → p4)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133650524503514140396241083557 : ((((p4 ∧ ((True ∨ ((p3 ∧ ((p4 ∨ p2) ∧ (p4 → ((p1 ∨ p5) ∨ p1)))) → p1)) ∨ p1)) ∧ (p3 ∧ p4)) ∧ p4) ∨ ((p3 ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231899477048949447948539778299 : (((False ∨ True) → False) → (((p5 ∨ (((p1 ∨ ((p3 → p3) ∧ (p2 ∧ p3))) ∧ False) ∧ (False ∨ p3))) ∨ p5) ∨ ((p2 ∧ p4) ∧ (False → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57163988400056331895560883421 : ((((p2 ∧ p1) ∨ p3) ∨ (p3 ∨ ((((((p1 → p4) ∧ False) → p1) → ((p4 ∨ p4) ∨ p4)) → p5) ∨ ((p2 ∨ (p4 ∧ False)) → p2)))) ∨ p3) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609125801553029938554971449891 : ((((((True ∨ (p3 ∨ (p1 ∧ (p2 ∧ p1)))) → (((False → ((p4 → p3) ∨ (p3 ∨ (p2 ∨ p2)))) ∨ (p2 ∨ p5)) → p3)) ∨ p4) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747899864500113561959091385107 : ((((False → p4) → (False ∨ ((p4 ∨ ((False ∧ p1) ∨ p5)) → (((((True → ((p4 → p5) ∧ p3)) → (p2 ∧ True)) ∨ p1) → False) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610503797844400459630354799012 : ((((((p2 → (((((((True ∨ (p1 ∧ (p5 ∧ p4))) ∨ p3) ∨ (p1 ∧ p1)) → True) → False) ∨ True) ∨ (p4 ∧ True))) → False) → p5) ∨ p3) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → (((((((True ∨ (p1 ∧ (p5 ∧ p4))) ∨ p3) ∨ (p1 ∧ p1)) → True) → False) ∨ True) ∨ (p4 ∧ True))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117785680049941544929193203865 : ((p4 ∧ (((((((False ∧ p3) ∧ (False ∨ p1)) ∧ p2) → False) → p4) ∧ (True → p5)) ∧ (((p1 → (p4 → p1)) → p3) ∨ False))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327855415047882209375644332821 : (True → (((p4 → ((p2 → p1) ∧ p5)) ∧ ((p5 ∨ p1) ∨ (((p3 → (p4 ∨ p3)) ∨ ((p1 ∨ (True ∨ True)) ∨ True)) → False))) ∨ (True ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118207052994863763692785315603 : ((p1 ∨ (((p1 → ((p1 ∧ (p4 ∧ (((p4 → ((p3 ∧ (p3 ∨ False)) → True)) ∨ p3) → (True ∧ False)))) ∧ p4)) ∧ p2) ∧ p2)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653619394753941881440655082351 : (((((((((((p5 ∨ ((False ∧ p1) → p3)) ∨ (True ∧ (True → p1))) ∧ False) → p4) → (p4 ∧ p1)) ∨ False) ∨ p5) ∧ p3) ∨ (True ∨ False)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_194023878789912180831318672462 : ((p4 ∨ (False ∨ ((p3 ∨ (p5 ∧ (p5 ∧ p1))) ∧ p3))) → (((p3 ∨ p5) ∨ p1) → ((False ∧ (p4 ∨ (p4 ∧ p1))) ∨ ((p1 ∧ True) ∨ True)))) := by
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
      cases h1
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- False on the left can always be used.
          apply False.elim h7
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
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h12 =>
            -- Conjunctions on the left can always be decomposed.
            let h13 := h12.left
            let h14 := h12.right
            -- Conjunctions on the left can always be decomposed.
            let h15 := h14.left
            let h16 := h14.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- False on the left can always be used.
          apply False.elim h20
        case inr h21 =>
          -- Conjunctions on the left can always be decomposed.
          let h22 := h21.left
          let h23 := h21.right
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h24 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h25 =>
            -- Conjunctions on the left can always be decomposed.
            let h26 := h25.left
            let h27 := h25.right
            -- Conjunctions on the left can always be decomposed.
            let h28 := h27.left
            let h29 := h27.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
  case inr h30 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h31 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h32 =>
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h33 =>
        -- False on the left can always be used.
        apply False.elim h33
      case inr h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h34.left
        let h36 := h34.right
        -- Disjunctions on the left can always be decomposed.
        cases h35
        case inl h37 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h38 =>
          -- Conjunctions on the left can always be decomposed.
          let h39 := h38.left
          let h40 := h38.right
          -- Conjunctions on the left can always be decomposed.
          let h41 := h40.left
          let h42 := h40.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56555070570904318293159167966 : (((p3 ∨ (p3 → (p2 ∨ False))) → (p2 → (((p2 ∧ False) ∨ ((p1 ∨ p5) → (False ∨ (p4 ∧ True)))) ∧ (p3 → (p5 ∧ (True → p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213802685788730600257977211375 : (((p2 ∧ (True → p2)) ∨ p5) ∨ ((((((p1 ∨ (p3 ∧ (p2 ∨ p2))) → p5) → p5) → p4) ∨ (False → p4)) ∨ (((True → p5) → True) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622946559741194314163989204768 : ((((p5 ∧ ((p5 ∧ ((((p4 ∨ p1) ∧ ((p3 ∨ p5) → p5)) ∨ p4) → p1)) → (((p1 → (p3 → True)) → p1) → (p4 ∨ p2)))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692678952194076420229610670934 : ((((((((p1 ∨ p5) ∨ p1) ∧ p1) ∨ p4) ∨ ((False ∧ (p3 ∧ False)) → p2)) ∧ ((((p5 ∧ False) ∧ p2) → (False ∨ (p1 ∧ p5))) → True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136746695946114001769837370961 : (((p1 ∨ p1) ∧ ((((p1 → (p3 ∨ p2)) → p3) → (p3 ∨ p4)) ∧ (p5 ∨ (False ∧ ((True → p4) ∧ (p1 → False)))))) ∨ ((p2 ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258783077277044122240582620880 : ((True → False) → ((((p1 → p3) → p1) ∨ (p4 ∧ (((True → (p3 → p3)) ∨ False) → (p3 ∨ p1)))) ∧ ((p2 ∧ (p3 → (True → p1))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134325871872423012577108806098 : (((p2 ∧ ((True ∧ (p1 ∨ (p3 → (p4 ∨ ((p5 ∧ ((p2 ∨ (p3 ∨ p1)) → p3)) ∧ False))))) → (p1 → p5))) ∨ p3) ∨ (p2 ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192390863544695355613818251206 : (((((p4 ∨ False) → (p2 ∨ (p3 → p2))) ∧ True) ∨ True) → ((True → ((p1 → ((p2 ∨ ((True ∨ p5) → False)) → p2)) → (p2 → p3))) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148495487594965912535946044185 : ((((p3 ∧ (p1 → False)) ∧ (((p2 ∨ (p1 ∧ p5)) ∨ p1) ∨ p2)) ∨ (((False ∧ p4) ∨ p5) → (False → p5))) ∨ ((False ∧ (p3 ∨ p5)) → False)) := by
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
theorem thm_5_vars_190560388517225673267658291479 : ((((p5 ∧ (p3 ∧ (p1 ∨ p5))) → (p1 → p3)) → p2) ∨ (((p5 ∧ ((True ∧ p3) ∧ p5)) ∧ p3) → (p3 ∨ ((p1 ∧ p1) → (p5 → True))))) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54118158129133169833328372268 : (((p5 ∧ ((p2 ∨ p5) → ((p2 ∧ p4) ∧ (p3 ∨ p5)))) → ((p3 → (p4 → False)) ∨ (((True ∧ p5) ∨ ((True ∧ True) → False)) ∨ p2))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741851440413248331063812214818 : ((((True → p5) ∨ ((p1 ∨ (((p2 → p4) ∧ p4) ∨ ((((((p2 ∧ p5) → p1) → p1) → (p3 ∧ p1)) ∨ (p2 → p3)) ∨ p3))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158323852394620147290599487877 : (((p3 → (p1 ∨ p5)) → ((p3 ∧ False) ∨ ((((p1 ∧ p4) ∧ p4) ∧ ((p2 ∨ p2) → p4)) ∨ True))) ∨ ((p5 → ((False → p5) → True)) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215867133996563898146030942902 : ((p2 ∨ (True → (False ∧ True))) ∨ ((p3 → p4) → ((((False ∧ (p1 ∧ True)) → (((p3 ∨ p1) → p4) ∨ (p2 ∨ False))) → False) ∨ (p4 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50252951373453441005539013924 : (((((p1 → p3) → (((((False ∧ True) ∧ ((False ∨ p2) → (p5 ∧ False))) ∨ p1) → p3) ∨ p4)) → p4) ∨ ((p4 ∧ p4) ∧ (False ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321596067665629213527489484326 : (p4 ∨ (p3 → ((((p2 ∨ p1) ∧ (p3 → (p3 → (p1 → (p4 ∧ ((True ∨ p3) ∧ ((p5 ∧ p4) ∧ (p1 → (p2 ∧ p2))))))))) → p2) ∨ p1))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h16 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h17 := h15 h16
    -- We need to get the left conjuct of h17 based on <expert-advice>.
    let h18 := h17.left
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351388715621863328993748869465 : (p4 → (((((((p4 ∨ p4) ∧ (p4 ∧ ((p2 → p4) → (p4 ∧ p1)))) ∧ (p2 ∨ False)) ∨ p5) ∧ p2) ∨ p4) ∨ ((p1 ∧ True) ∧ (False ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313989343303567679103672167033 : (p3 ∨ ((((p2 ∨ p4) ∨ True) ∧ (p3 ∧ ((p2 ∨ p1) ∨ ((True ∨ ((True ∨ False) ∧ p2)) ∨ ((p5 ∧ p4) ∧ (p1 ∧ True)))))) ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50295502399710757252382728432 : (((((p4 ∨ (p2 ∧ ((((False ∨ (p1 ∧ p2)) ∧ p1) → p2) → p2))) ∨ p3) ∨ (p1 → (p1 → True))) ∨ (((p1 ∧ True) → p4) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41323780006797539127894213089 : ((((p4 ∧ (((False ∨ p1) ∨ p1) → (p1 → ((p2 ∧ True) → (True → (p4 ∧ False)))))) ∧ (((p5 ∧ (p1 → p1)) ∨ p1) ∨ p5)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307383844994873542363701456870 : (p1 ∨ (p4 ∨ ((((p2 → (p3 ∧ ((p5 → p3) → p1))) ∧ (False ∧ False)) ∧ (p3 ∨ True)) ∨ ((p4 ∧ p2) → (((p3 → p4) ∨ p5) ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165598831361440994121321067484 : ((((p5 ∧ ((p2 ∧ (p3 ∧ p5)) ∧ p2)) → False) → (p5 ∧ (True ∨ ((p2 ∧ p5) ∧ p5)))) ∨ (((p2 ∧ (p3 ∨ True)) ∧ True) → (p5 ∨ True))) := by
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
theorem thm_5_vars_248148702161734573763627285286 : ((p2 ∨ False) ∨ ((p2 ∨ (((p1 → (((True ∧ p3) → ((p4 ∨ (False ∧ False)) ∨ False)) ∧ p3)) ∨ True) ∧ (p3 ∨ (p4 → p4)))) ∨ (False ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313046065396228547464471822712 : (p3 ∨ ((((False ∧ ((False ∨ (True → ((p2 ∨ (p2 → (p2 → True))) ∨ p1))) ∧ (True ∨ p5))) → (p1 ∨ (False ∨ (p2 → p4)))) → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207669117834928727340438972007 : ((((p5 ∨ False) ∨ (p1 ∧ p2)) → p5) → (((True → (p3 ∧ p5)) ∧ (False ∨ (False ∨ p2))) → (((p4 ∨ (p3 ∧ (p1 → p2))) ∧ p4) ∨ p5))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h9
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314566415371182812664236338291 : (p3 ∨ ((p2 → (p3 ∨ (p5 ∧ ((p2 ∨ p3) ∧ (p4 ∧ (p1 → (p1 → (p1 ∧ (p5 ∨ p4))))))))) ∨ (True ∨ (True → (p1 ∧ (True ∧ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765452798050881831867563647298 : (((p4 ∧ ((p4 → (p1 ∧ (p2 → ((((False ∨ (True → (p4 ∨ p1))) ∨ (p3 ∧ p3)) ∨ p3) → True)))) ∨ (((p5 ∧ p2) → p3) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42154599766137010978999114375 : ((((p1 → p3) → ((p1 ∧ ((((p3 → (True ∧ p1)) ∧ (p5 → p3)) ∧ False) ∧ (p3 ∧ (p4 → (p5 ∨ (p4 → True)))))) ∧ p4)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782471394079067772918900228650 : (((p3 ∨ (((((p3 → ((p2 ∨ p5) ∧ p1)) ∧ (p5 ∧ False)) ∨ p1) → ((((p1 ∧ p2) → False) → (p4 ∧ p4)) ∨ (True ∨ p2))) ∨ False)) ∨ p4) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249532655318533847121267867489 : ((p5 ∨ p2) ∨ ((((p3 ∨ ((p4 → p5) → (True → False))) → ((p1 → (p1 ∨ (p1 → True))) ∧ (p4 → (p1 ∨ (p4 ∨ False))))) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118430851243321441042692585058 : ((p2 ∨ (p5 ∨ (p1 ∧ (p1 → ((p5 → (p5 → (((p2 ∧ (p4 → ((p1 ∨ p1) → p4))) ∨ p3) ∧ (p3 ∨ p1)))) ∧ p4))))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669042463364425337101318239535 : ((((((p4 → ((((False → p1) → True) → (p5 ∨ (((p2 ∧ p3) → (p2 ∨ True)) ∨ False))) ∧ False)) ∨ p3) → p4) ∨ ((True ∧ True) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_174309679651393102704143836411 : ((((p3 ∨ ((p2 ∨ True) ∧ True)) ∧ ((p2 ∨ p2) → p2)) ∨ ((p4 → p4) ∧ p5)) → (p1 → (((False ∨ p2) ∨ (False → (False ∧ p4))) ∨ p5))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h7
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h13
        -- False on the left can always be used.
        apply False.elim h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117531308683664733221701608145 : ((p2 ∧ ((((p5 ∧ ((p4 ∨ (p3 ∨ True)) ∧ (((p5 → p5) → (p5 → (p5 ∨ p5))) → p2))) → p5) → p5) ∧ (p2 ∨ p2))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60127886911663185350906404318 : (((p4 ∨ True) → ((((p5 ∧ p4) ∨ p4) ∨ ((True → ((False ∨ True) → p2)) → ((False ∨ p5) ∧ (False → p2)))) ∨ (p4 ∨ (p2 → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



