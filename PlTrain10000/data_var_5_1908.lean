variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110774146728466818956626570000 : (((((((p5 ∧ p3) ∨ (((p3 → p5) ∨ (p4 → ((True ∨ ((p1 ∧ False) ∧ p1)) ∨ p4))) ∧ True)) ∨ False) ∧ p1) ∨ False) ∧ p2) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42320110088468401170246007778 : (((p2 ∧ (p4 ∧ ((((False ∨ (True ∨ p4)) ∨ (True ∧ ((p1 ∨ (p3 ∧ False)) → False))) ∧ p2) → (((p3 → p2) ∧ p5) ∧ p4)))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112532615356006118815671818588 : (((((((True → (p1 → ((p3 ∨ (p5 ∧ (True → True))) → p5))) ∧ (p5 ∨ p2)) ∧ p1) ∨ (False ∨ (p5 → False))) → p3) → p2) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787153366424684362534063895360 : (((p4 ∨ ((p5 ∨ p1) → ((p2 ∨ ((((p1 ∧ (p3 → True)) ∧ (True ∧ True)) ∧ (p4 ∧ (True ∨ p5))) ∨ (p1 ∨ (p2 ∧ True)))) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130587727969941194886649340646 : ((((True ∧ (False ∨ p3)) ∨ (((False → p1) ∨ p3) ∧ ((p1 ∨ (p1 → p1)) → True))) ∧ ((p3 → (False ∧ p2)) ∨ True)) ∧ ((p4 ∧ p5) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774801836864457184056772035650 : (((False ∨ ((((p4 → (p1 ∨ p1)) → p5) ∨ p2) → ((p4 → p1) ∨ ((True ∨ (((True ∨ p2) ∧ p5) ∧ ((p1 ∨ p5) ∨ False))) ∨ p4)))) ∨ False) ∧ True) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42610218687746587499509855457 : (((p3 ∨ ((False ∧ (p3 → ((((False ∨ (p2 ∨ (p2 → ((p4 ∨ (p2 ∧ p5)) → (p5 ∧ p4))))) ∨ p1) → True) ∧ p5))) ∨ p2)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160050081821668446438328394264 : (((True ∧ ((p4 ∧ p5) ∧ (True ∨ (((p1 ∧ (p2 ∨ p1)) → (p5 → p3)) → (p4 → False))))) → p5) → ((True ∧ ((p2 → False) ∧ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49349180242724028544111968251 : (((p1 → (((False → (p5 ∨ False)) → ((False ∧ (((p4 ∨ p1) ∧ (True → (p3 → p2))) ∨ p4)) → p1)) → p4)) ∨ (p1 → (p1 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38357265000757892009937855669 : ((((((p3 → (p5 → (p2 ∨ False))) ∨ (((p5 → p1) ∨ p5) ∧ (p1 → True))) ∨ p2) ∨ (True → ((True → True) → (p5 ∨ p4)))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67841148327994337460181003146 : ((p2 → (((((False → (p1 ∨ ((False ∧ True) ∨ True))) → p5) ∧ p4) ∧ (((p4 ∧ p5) ∨ (p3 ∧ p5)) ∨ (True ∧ p3))) ∨ (True → True))) ∨ p5) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622827509547418596061881581845 : ((((p5 ∧ ((((p2 ∨ p1) ∧ (p4 ∨ p4)) → (True ∧ (((p1 → (p5 → True)) ∨ True) ∧ ((p1 ∨ p5) → (p5 ∧ False))))) ∧ p4)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193942110365859982207890604159 : ((p2 ∨ (((True ∨ (p4 ∧ p2)) → (p5 ∨ p5)) → p2)) → ((p5 → (((p3 ∨ False) ∨ p2) → p2)) → (True ∧ (p3 ∨ (p4 ∨ (p1 ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319448449990863822990992897792 : (p4 ∨ ((((((True → ((p5 → p3) → False)) ∧ False) ∨ p5) ∨ True) ∨ p2) ∨ (((p5 ∨ True) → p2) ∧ (((True → (p1 ∨ True)) → p2) ∧ False)))) := by
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
theorem thm_5_vars_146945286320140583472181060933 : (((((((p5 → ((p3 ∨ p1) ∨ p4)) → (p2 ∨ p5)) ∧ False) ∧ ((p3 ∨ False) ∧ (p2 ∧ False))) ∨ p5) ∧ False) ∨ (False → (p3 ∧ (True ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246420027448193814865112467197 : ((p5 ∧ True) ∨ (p2 ∨ ((((((((p5 ∧ True) ∨ p3) ∨ False) ∧ p2) ∨ p5) → False) ∧ p5) → ((((p2 → (p2 → p5)) → p1) ∧ True) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (((((p5 ∧ True) ∨ p3) ∨ False) ∧ p2) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : (((((p5 ∧ True) ∨ p3) ∨ False) ∧ p2) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h9
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593727066489177444976816739642 : (((((((True ∧ (True → p2)) ∨ p5) ∨ ((((p4 ∨ p3) ∧ ((True ∧ p3) → p2)) ∧ p1) ∨ p1)) ∧ (False ∧ (False → (False ∨ p4)))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670139553327839276018837973340 : (((((p5 ∨ ((p4 → p4) → (p5 ∧ p5))) ∨ (p1 ∧ ((False ∧ p4) → ((False ∨ (False ∧ (p4 ∧ True))) → p1)))) ∨ (p5 → (p1 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788989018057373285923601752215 : (((p5 ∨ ((p5 → (True → ((((p4 ∨ ((p4 ∧ (True ∨ p1)) → p1)) → p2) ∧ p5) → (p3 ∧ ((p1 ∧ p1) ∧ p1))))) ∨ (p4 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192711575964996932790579412716 : ((((p1 → (p3 ∨ True)) ∧ ((False → p5) ∨ p3)) → p5) → ((((p5 ∧ (p3 → (p4 ∧ ((p4 → (p2 → p4)) ∨ p5)))) → False) → p2) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 → (p3 ∨ True)) ∧ ((False → p5) ∨ p3)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620166457439076860386183061190 : (((((p2 ∧ p1) ∨ (p1 ∧ ((((((p5 ∨ (True ∨ True)) ∨ True) → p4) ∧ ((p2 → ((p5 ∧ p3) ∧ False)) → False)) ∨ True) ∨ True))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_206366011277321606369366197700 : ((p2 ∨ (p2 ∧ (p1 ∧ (False ∨ False)))) ∨ ((True ∨ (p5 → (p2 ∨ (((((p4 → p1) ∨ p2) ∨ (p5 ∧ True)) ∧ (p5 → p3)) ∧ False)))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138175847835489825954492312577 : ((p1 → (((p3 → (True ∨ p3)) ∨ p4) ∧ ((p3 ∨ (p3 ∧ (p2 ∨ p2))) ∨ (p2 ∨ ((p5 ∧ False) → (p1 → p5)))))) ∨ ((True ∧ p2) ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53703532621587269155265105981 : (((False ∨ (((p2 ∨ p4) ∨ (p1 → p1)) ∧ (p4 ∧ p1))) ∧ (((True → p2) ∨ ((p5 → (False ∧ (p2 → (p5 ∧ p1)))) ∨ True)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705857528750728515247770545519 : (((((p1 ∧ (False ∧ p1)) ∧ (p4 → (p1 ∧ True))) ∧ (p5 ∧ (p5 ∧ ((p1 → ((p2 ∧ p1) ∧ p4)) ∨ (((p5 → p4) ∧ p1) ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191202879166859779092878489281 : ((((p5 → p3) ∨ p4) → ((p1 → (p3 → p5)) ∨ True)) ∨ ((((p5 → ((p4 ∧ p5) → (p3 → (True ∧ p3)))) ∧ p5) ∧ (False → p2)) ∧ p5)) := by
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
theorem thm_5_vars_50859107394383355870548960263 : ((((((p5 ∨ (True → ((p3 ∧ True) → p5))) ∧ True) ∧ ((True ∨ False) → (p4 ∨ p5))) ∨ p3) ∧ (((True ∨ p4) → True) ∨ (p4 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719834370139173362772020736806 : ((((p3 → ((p1 ∨ False) ∨ p4)) ∨ ((p5 → (((((p2 ∧ p2) → ((p1 ∧ p2) ∨ ((True ∨ p3) ∧ p2))) → p2) → p3) ∧ False)) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_788349344184257890959686935131 : (((p5 ∨ (((((p3 ∧ p2) ∧ ((True ∨ False) → p2)) → ((False ∧ (p4 ∧ ((p5 ∨ True) → p4))) → (p5 → (True ∨ p3)))) → p2) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204323186331418081128749567460 : (((p3 ∧ ((p1 ∨ p4) ∧ True)) ∧ p5) ∨ (p1 → (((p4 → p4) → False) ∨ (True ∨ ((True ∨ ((False → p2) → (p1 ∧ p4))) ∧ (p3 ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315716774261077506836844814264 : (p3 ∨ ((True → False) ∨ ((p1 ∨ p5) ∨ (p5 → (p4 → (p1 ∨ ((p5 ∨ ((((p1 → p2) ∨ p5) ∧ (p5 ∧ True)) ∧ p5)) ∨ (True ∧ p5)))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205173379844153151779305648657 : (((False ∨ (p1 ∧ p1)) ∧ (p2 → p1)) ∨ (((p4 → (p2 ∧ ((False ∧ ((p5 ∧ p5) ∨ p1)) ∨ p1))) ∨ p2) ∨ ((True ∨ (p1 ∨ p1)) ∨ False))) := by
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
theorem thm_5_vars_356886220180793618510900893053 : (p5 → (((True → (p5 ∨ True)) ∧ p4) → (((p3 → (p4 → ((p1 ∨ (True ∧ (True ∧ (p2 ∨ (p1 ∨ p2))))) ∧ True))) → (p1 ∨ p2)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2304033405229275736934197995 : ((((True → False) ∧ (True ∨ ((((p3 → p3) ∧ True) ∨ p2) → p1))) ∨ p4) → (p4 ∨ (p5 → ((p1 ∧ ((p4 ∧ p5) → p1)) → False)))) := by
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
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h7 := h3 h6
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h9
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245401790553075991622610200455 : ((p2 ∧ p4) ∨ ((((True → ((((True → ((p5 ∧ (p2 → (True ∨ (True ∨ p5)))) ∨ p2)) ∧ (False ∧ True)) ∨ p4) ∧ p4)) ∨ p3) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137379148212317445528475142594 : ((p3 ∧ (((p5 ∧ (p2 → (p1 ∧ (p4 ∨ p1)))) ∨ p3) ∨ (((p5 ∨ True) ∨ p1) ∨ (p4 ∧ (p2 ∧ (p1 ∨ False)))))) ∨ ((p1 ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206999690752883386371431329558 : ((((p4 → p1) ∧ (False → False)) ∧ p1) → ((((p3 ∨ (p1 → ((p1 → ((p4 ∨ (p1 ∧ p1)) ∧ p4)) → p5))) ∨ p5) ∨ (p4 → p4)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181419615526495081206775852062 : ((p2 ∨ (p1 ∧ ((p2 ∨ (False ∧ (p3 ∧ p1))) ∧ ((p1 ∧ False) → p4)))) → (p1 ∨ ((p4 ∨ p4) → (p3 ∨ (((p4 → p5) ∨ p2) ∨ p3))))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118247278758704865688748040528 : ((p1 ∨ (((True ∨ (p5 → p2)) ∨ ((p1 ∧ ((((False ∨ (p1 ∧ p5)) ∧ (p2 ∨ False)) → True) ∨ p4)) ∧ p3)) → (p4 ∨ p1))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251011388661512182012660216504 : ((p1 → p5) ∨ ((((((False ∧ False) ∨ p4) ∧ ((p4 ∨ p4) ∨ p1)) ∧ (p3 ∨ p2)) ∧ p4) ∨ ((((p1 ∨ True) ∧ p1) ∧ p2) ∨ (True ∨ p1)))) := by
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
theorem thm_5_vars_244816219845175114161902658285 : ((p1 ∧ p1) ∨ (((((p3 ∨ p1) → p5) ∨ ((p2 ∨ p5) → p2)) → (p4 ∨ ((True ∨ True) ∨ p4))) → (p3 ∨ (p4 ∨ (p1 → (p3 ∨ True)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137111716376122233131343659250 : ((True ∧ (((p5 ∧ (((((p1 ∨ p3) ∧ p2) ∨ False) ∨ p4) ∧ p5)) → False) → (((p1 → (False → p1)) ∨ p2) ∧ p1))) ∨ (True ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197491577969867224518918756537 : (((p2 ∧ ((p2 ∧ False) ∨ False)) ∧ (False ∨ p2)) ∨ (((((((p5 → p5) ∧ p4) ∨ (True ∨ (p1 ∧ p5))) → False) ∧ (p2 → p1)) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184247700320257100178582272555 : ((((False ∧ ((p1 ∧ (p2 ∧ (p3 → p4))) ∧ p4)) → p1) → p5) ∨ (p1 ∨ (((p3 → (p1 ∧ p3)) ∨ ((False → (True → p4)) → True)) ∨ p2))) := by
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
theorem thm_5_vars_671414263786299098964221236753 : ((((p1 → ((True → ((True ∨ ((p1 → False) → ((p4 ∧ False) ∧ p1))) → (p3 ∧ p5))) ∨ ((p2 → p4) ∨ p3))) ∨ ((p1 → p2) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1764983829104960525696453766 : (((((p3 ∨ (((p1 → p2) → True) ∧ p3)) → ((((False → (p4 ∧ True)) ∨ True) → p2) → p2)) → p5) ∨ True) ∨ ((p5 → True) ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_382603006580194765196150483675 : (((((((p3 → (p1 ∨ p5)) ∧ p1) ∧ (((((p3 ∨ False) ∨ ((p5 ∨ p5) ∨ True)) ∧ p5) ∧ (p2 ∨ False)) ∧ (p3 ∨ True))) ∨ p4) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_168669436213056874881871136799 : ((p5 ∧ ((p4 → (((True ∧ p2) ∧ p2) → (((True ∧ False) ∧ p1) → (p4 ∧ p4)))) ∨ p5)) → ((p3 → ((p4 ∨ False) ∧ p1)) ∨ (False ∨ p5))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158795416868738770957991350159 : ((p5 ∧ (((p3 ∧ (((True ∧ True) ∧ p2) → p3)) ∧ True) ∧ (False ∨ ((p1 ∨ (p5 ∧ p1)) → p2)))) ∨ (((p4 ∨ p3) ∨ True) ∨ (p3 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178775726774146588255538673149 : (((True ∨ (p5 ∧ p1)) ∧ ((p5 → ((p1 → p4) ∨ p5)) → (p2 ∧ p5))) ∨ ((((p3 → p3) ∨ False) ∧ p3) → ((False ∨ p3) ∨ (False ∧ p5)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792994521964602086823357410635 : (((True → ((p3 ∧ False) ∨ (True → ((((p4 → (False ∨ (p4 ∨ p3))) ∧ ((p4 → False) → (p3 ∨ (p1 ∧ (False ∨ p4))))) ∨ p5) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137205344029858363321805843877 : ((False ∧ (p4 ∨ (((p5 → True) ∨ ((((p5 ∨ p2) → (p5 → False)) ∨ p4) ∨ (((p4 → p4) ∧ True) ∨ p5))) → False))) ∨ (p3 ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191315953156566672494458582065 : (((True ∧ p1) ∨ ((p3 ∧ (p5 ∧ (p4 ∧ False))) ∨ p2)) ∨ ((p4 ∧ p4) → (((p4 → True) → p2) → (True ∧ (((p1 ∧ p2) → p2) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184323097871821151256381163992 : ((((p4 → p1) ∨ ((True → (p2 ∨ (p1 ∧ False))) ∨ p3)) → False) ∨ ((((p4 ∧ ((p2 ∨ p2) ∧ False)) ∧ p4) ∨ (p2 ∨ (False → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44338687687584628059609114864 : (((((((p5 → p2) ∨ ((p1 ∧ (p5 ∨ p5)) ∧ p4)) → (p1 → p5)) ∨ (p2 ∧ False)) → ((p4 ∨ (p5 ∧ (p1 ∨ p2))) → False)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231887606515758788629622654464 : (((True ∨ p4) → True) → ((p3 → (p3 → p5)) → ((p3 ∧ (True ∨ (((p1 → ((True ∨ p3) ∧ (p5 ∧ p1))) ∧ p3) → p1))) → (p4 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h12
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h15 := h13 h14
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110816480172771482429529327604 : (((((p4 ∧ (True ∨ (True ∨ True))) ∧ (p5 ∧ ((((p4 ∨ p5) ∨ p1) → p4) ∧ (True ∧ (p3 → (p5 ∨ True)))))) ∨ True) ∧ p5) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147914667891998721707802480997 : ((((((p3 → ((False ∧ (p4 ∧ (False ∨ p1))) → (p2 ∨ False))) ∨ p1) ∨ p3) → (p5 ∨ p4)) ∧ (True ∧ p4)) ∨ ((False ∧ False) → (p5 ∧ p2))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244565143403870255807592046373 : ((False ∧ p4) ∨ (((p3 ∨ ((False ∨ p1) ∨ (p5 ∨ p1))) ∧ (((False → p3) ∨ p2) → ((((p4 → p2) ∧ p1) ∨ p1) ∧ p5))) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53703827697635024734215265455 : (((False ∨ ((p4 ∨ ((p3 → p3) → p2)) → (True → p4))) ∧ (p3 ∨ (True → (False ∨ (((((p5 → True) ∨ p4) ∧ p2) → p4) ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225906867202665793263044705416 : (((p1 ∧ p4) ∨ p2) ∨ ((False ∧ ((False ∨ p1) → (((True → p3) ∧ p5) → ((True → p2) ∨ p1)))) ∨ (True ∨ ((p1 ∨ (True ∨ p4)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148436473625812776179943918625 : (((True ∨ (p2 ∨ ((p2 ∧ (p2 ∨ True)) ∨ (p2 ∨ ((p1 → p2) ∨ p3))))) → ((p4 ∨ (p4 → p4)) ∨ p1)) ∨ ((p1 → (p3 ∨ p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52451153841405383145492208833 : (((p3 ∧ (p1 → ((((p2 ∨ p3) ∧ ((p2 → p2) ∧ p1)) ∧ p3) → p2))) ∧ ((((p1 ∨ p5) → (p2 ∨ p2)) ∧ False) ∨ (True ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114372505600964212327037614744 : ((((p1 ∨ (p2 ∨ ((p3 → (p5 → (True ∧ p2))) ∧ (((p3 ∨ True) ∧ p2) ∧ False)))) ∨ p5) ∨ (True → (True → (True → True)))) ∨ (True → False)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57348321058302320836455669966 : (((p2 ∧ (p2 → p5)) ∨ ((p2 ∨ ((p1 ∧ ((((p4 ∧ p2) ∨ p3) ∨ p5) ∧ p3)) ∨ p1)) ∨ (True ∨ ((True ∧ True) ∧ (p1 ∧ p4))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159304303885453093134230325135 : ((p5 → ((p1 ∨ ((p4 ∧ (True ∨ p2)) ∧ ((p5 ∨ (p2 ∧ ((p1 ∧ p3) → p4))) ∧ p4))) ∧ True)) ∨ (((p1 → False) ∨ p4) → (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193940207168838694130020931862 : ((p2 ∨ ((p3 → ((p2 → False) ∧ (p3 → p1))) ∨ p3)) → ((((((p3 ∨ True) → p5) ∨ False) → p2) ∧ ((p4 → (p1 → p1)) ∨ p1)) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
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
theorem thm_5_vars_219590919957814413263595383650 : ((True → (p5 ∧ (p2 ∧ False))) → ((p2 → (p1 ∧ ((((((p1 ∧ p3) ∨ False) ∨ True) ∨ p5) → p1) → (p1 → (p4 ∨ p3))))) ∨ (p4 → p4))) := by
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117421199618667772893630474772 : ((p1 ∧ ((p3 ∧ (((p3 ∧ p5) → p4) → ((True ∨ ((p2 ∨ (p1 ∧ True)) ∨ (p5 ∧ True))) ∧ (p5 → p1)))) → (p5 ∧ False))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347359259119720995326441568672 : (p3 → ((p3 ∨ ((p3 → ((p5 ∧ p2) ∨ p1)) ∧ False)) ∧ (p5 → ((False ∨ p5) ∧ ((((p5 ∨ ((False ∨ p5) → p1)) → False) ∨ p3) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175200028886957487315466220029 : ((False ∨ ((((p1 ∧ p2) ∧ p2) → ((p2 → p5) ∨ p2)) → (p2 ∧ (p4 ∧ p5)))) → ((p2 ∧ (p4 → p1)) → (True → (p1 ∨ (False ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : p4 := by
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h9 : (((p1 ∧ p2) ∧ p2) → ((p2 → p5) ∨ p2)) := by
        -- Implications on the right can always be decomposed.
        intro h10
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Conjunctions on the left can always be decomposed.
        let h13 := h11.left
        let h14 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h15 := h7 h9
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- We need to get the left conjuct of h16 based on <expert-advice>.
      let h17 := h16.left
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h18 := h5 h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111582418813509788704888093066 : ((((p3 ∧ ((((p3 → ((p4 → p5) ∨ True)) → p3) ∧ (p2 ∧ p5)) ∧ ((p4 → (p3 ∨ False)) → (p1 ∧ p2)))) ∧ p1) ∨ True) ∨ (p1 ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47281801846726986960008790975 : ((((p5 ∨ ((p2 ∨ p2) ∨ p4)) ∨ (True → ((((((p2 ∨ p2) ∨ p1) → p4) → False) ∨ ((p5 → p3) → p1)) ∧ False))) ∨ (p3 ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227020464516144951418879447401 : (((p2 ∨ True) → p2) ∨ (True ∧ (((p3 → (True ∧ False)) → ((p4 ∨ (p4 → (p5 ∧ p5))) ∨ True)) ∨ ((((True → p3) ∧ False) → p3) ∨ p2)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184419947690151486044008227855 : ((((p3 → (p4 ∨ (p3 ∨ (p1 ∧ True)))) → False) ∧ (False → p1)) ∨ ((True ∨ (p3 → (False ∧ ((((p4 → p3) → False) ∨ p1) ∨ p3)))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314422122669142082035834677564 : (p3 ∨ (((((p3 ∨ (((True ∨ p2) ∧ True) → p3)) → p4) → p4) → (((p3 ∧ p1) ∨ (p5 → p1)) ∧ p5)) ∨ ((False → p5) → (True → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186672463671489312771813162388 : ((((p3 → p3) ∨ ((p5 → p2) → p2)) ∧ ((True → p3) → p4)) → (((True ∨ True) → (p4 ∨ True)) ∨ (((p4 ∧ (p3 ∧ p4)) ∨ p4) ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
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
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355910497533627686200224833631 : (p5 → ((((p4 → (p3 ∨ (p1 → p3))) → ((False ∨ p5) ∨ (p3 → (((False → (p2 ∨ p4)) ∨ True) → p2)))) → p3) → (p3 ∨ (p5 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p4 → (p3 ∨ (p1 → p3))) → ((False ∨ p5) ∨ (p3 → (((False → (p2 ∨ p4)) ∨ True) → p2)))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684689688888319330775633146233 : (((((True ∨ (p3 ∧ p2)) → ((p5 → ((p2 ∨ True) ∨ p3)) ∧ (False ∧ (p1 ∧ (False → p3))))) ∨ ((p1 → p3) ∨ ((p5 → p4) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354606368312936328781614473526 : (p5 → ((((((p1 ∨ (True ∨ (p1 ∨ p4))) ∨ p5) ∨ ((p3 ∨ ((p3 → p2) ∧ (((p3 → p5) ∧ p4) ∧ p2))) ∧ p4)) → p3) ∨ p2) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114346789390918406981306509239 : (((p5 ∨ (p1 → (False ∨ (((p5 ∨ True) ∨ False) → (((p5 → False) → p2) ∨ (p3 ∨ False)))))) ∧ (((p3 ∧ p5) → False) → p5)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86589411660759613891697070762 : (((((p4 → p4) ∧ (p4 → (True ∧ True))) → False) ∧ (p2 → (((p2 ∨ (p4 ∧ (p5 ∨ (p2 ∧ ((False ∧ p4) → False))))) ∧ p3) ∧ False))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p4 → p4) ∧ (p4 → (True ∧ True))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121398715425592011493847706712 : (((((p5 ∧ ((p1 ∨ p2) ∧ p4)) → ((p2 → (p3 ∨ p5)) → (((((p3 ∨ p2) → p3) → True) → False) ∧ p3))) ∨ p2) → p3) → (p2 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p5 ∧ ((p1 ∨ p2) ∧ p4)) → ((p2 → (p3 ∨ p5)) → (((((p3 ∨ p2) → p3) → True) → False) ∧ p3))) ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60535888944644262049898435312 : ((True ∧ ((((False → (((p1 ∧ p1) ∧ p4) → (p5 → p5))) ∧ (p4 ∧ (True ∧ (p4 ∧ False)))) ∨ (((p2 → False) → False) → p2)) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318867655386388597158277142521 : (p4 ∨ (((p1 ∨ (p2 ∧ (p2 ∨ ((p3 ∨ p1) → (p2 → ((p5 ∨ p1) ∨ ((p4 ∨ p2) ∧ p1))))))) → (False ∧ p2)) ∨ ((p1 ∨ True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349960352296629642231109886613 : (p4 → ((((p1 ∨ p5) ∧ (True ∧ (p2 ∨ (p3 ∨ (p1 ∨ (p5 ∨ ((((p1 ∨ (True ∨ (p5 ∧ p3))) ∧ p4) ∨ p4) ∧ p3))))))) ∧ p2) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226199963381658146827741245577 : (((p2 ∨ False) ∨ p3) ∨ (((True → ((p2 ∨ (p2 → (p4 → (p2 ∧ False)))) ∨ (False → (p2 → p4)))) ∧ (p1 ∧ (p1 ∧ p1))) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234042107947186909611457133285 : ((p5 ∨ (p2 → False)) → ((True ∧ p3) → (((((p5 ∧ (p5 ∨ (((p5 → p5) ∨ p1) → False))) → (True → (p4 ∨ True))) ∧ False) ∨ p1) ∨ p3))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260281291746089755941868789893 : ((p2 → p4) → ((((((p5 → False) ∨ False) ∧ p2) ∨ (((p1 ∧ p5) ∧ ((True → p4) ∨ ((True ∨ p4) → p5))) → (p3 ∨ p5))) ∨ p1) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254927569017048870868036212640 : ((p4 ∧ True) → (p2 → ((p4 → ((((p5 → p4) ∨ p1) ∧ p3) ∨ ((((p2 → p3) ∧ False) ∨ (False → False)) ∧ (p5 ∧ (p2 ∧ True))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180280283815336082106930701210 : (((p3 → (p4 ∨ ((((p2 → p5) ∨ p3) ∨ p1) → (p3 ∨ p1)))) → False) → (True ∧ ((True ∧ p4) ∧ (p1 → (p5 ∧ (p3 ∨ (p5 ∧ p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → (p4 ∨ ((((p2 → p5) ∨ p3) ∨ p1) → (p3 ∨ p1)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- False on the left can always be used.
  apply False.elim h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : (p3 → (p4 ∨ ((((p2 → p5) ∨ p3) ∨ p1) → (p3 ∨ p1)))) := by
    -- Implications on the right can always be decomposed.
    intro h12
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h17 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h18 := h1 h11
  -- False on the left can always be used.
  apply False.elim h18
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h19 : (p3 → (p4 ∨ ((((p2 → p5) ∨ p3) ∨ p1) → (p3 ∨ p1)))) := by
    -- Implications on the right can always be decomposed.
    intro h20
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h21
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h24 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h24
    case inr h25 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h20
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h26 := h1 h19
  -- False on the left can always be used.
  apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42835739823052117529347479034 : (((p1 → (p4 ∨ (True → (((False ∨ True) ∧ p2) → ((p4 ∨ (p4 → (p2 ∧ (p5 → p4)))) ∧ ((p5 ∨ (p3 ∨ p2)) ∧ p3)))))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_892436180292379878228553612244 : (((((((p3 ∧ p2) ∧ (True → (p5 ∧ p4))) ∨ ((False ∧ (p1 ∨ p2)) ∨ ((False ∨ True) ∨ (p4 ∨ p4)))) → p2) ∧ (p5 ∧ (p3 ∨ p1))) → p2) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : (((p3 ∧ p2) ∧ (True → (p5 ∧ p4))) ∨ ((False ∧ (p1 ∨ p2)) ∨ ((False ∨ True) ∨ (p4 ∨ p4)))) := by
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
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : (((p3 ∧ p2) ∧ (True → (p5 ∧ p4))) ∨ ((False ∧ (p1 ∨ p2)) ∨ ((False ∨ True) ∨ (p4 ∨ p4)))) := by
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
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656296081800975930251042083587 : ((((((((p2 ∨ False) ∨ p3) ∧ ((True ∨ p3) ∧ (p4 ∧ False))) ∧ False) ∨ (p1 → (p2 ∧ (p4 → (p3 ∧ (p1 → True)))))) ∨ (p3 ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_344211633451391010246992164654 : (p2 → (p1 ∨ (p4 ∨ ((p2 → (((((p2 → True) ∨ p2) ∨ p4) → p2) ∨ p5)) → (((p4 → p1) ∨ (p2 ∨ (True ∨ p2))) ∨ (p3 ∨ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114336779185705657739553646034 : (((p5 ∧ ((p1 ∧ (((p1 ∨ p4) ∨ (((p3 → p2) ∨ (p5 ∧ p1)) → p5)) → p3)) ∨ p4)) ∧ ((False ∧ p2) ∨ (p4 ∨ p4))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193231475727685778528451450669 : ((((True ∨ p5) ∨ p1) ∧ (p4 → (p1 ∧ (False ∨ True)))) → ((p4 ∨ (((p2 ∨ False) ∨ True) ∧ ((p2 → p4) ∨ (False → (False ∨ p5))))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
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
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
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
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
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
    intro h10
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43569482466997145019494192556 : (((((True ∨ (((True ∨ p3) ∨ (((p5 ∧ (p2 → ((p3 → True) ∧ p1))) → p5) ∧ (p4 ∨ False))) ∨ (p3 → p5))) ∧ False) → False) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61946325464274266608731461302 : ((p2 ∧ (((p1 ∧ ((p1 ∧ ((p1 ∧ p1) ∨ p2)) ∨ ((p1 → False) ∨ (p5 → True)))) ∨ True) → ((p1 → ((p4 → True) → p4)) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88115247751515422528345288701 : ((((p5 ∨ (p5 → p5)) → p1) ∧ (((((p1 → (True → (p4 ∧ ((((False ∨ p4) ∧ p4) ∨ True) ∧ p3)))) ∨ True) ∧ True) ∨ False) → False)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((p1 → (True → (p4 ∧ ((((False ∨ p4) ∧ p4) ∨ True) ∧ p3)))) ∨ True) ∧ True) ∨ False) := by
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
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



