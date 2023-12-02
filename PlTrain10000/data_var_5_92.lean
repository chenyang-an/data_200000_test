variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204635108050303868317509535858 : (((False ∧ (p5 ∧ (p4 ∧ p4))) ∨ p4) ∨ ((p3 ∨ False) → ((p1 ∨ p1) ∨ ((True ∧ (True ∧ (True ∨ (p4 ∧ p1)))) ∧ ((p5 → p2) → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45353325425955872920854410242 : (((p4 ∧ (((p1 ∨ p3) → (((p5 → p5) ∧ ((p3 → ((((p3 → p5) ∨ p2) ∧ p3) ∧ (p4 ∨ p1))) ∨ p4)) ∨ p1)) → p3)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58355380795816200988588298610 : (((p1 ∨ True) ∧ ((p3 ∧ (((p2 ∧ ((p2 → p5) ∧ (((p3 ∨ p4) → True) → ((p1 → p1) → (p3 → True))))) ∧ p5) → False)) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147484052694714644086463184425 : (((p4 ∧ (((True ∨ p2) → (True ∧ ((((False → p5) → p1) ∧ ((p4 ∨ False) ∧ p4)) ∨ True))) ∧ p5)) ∨ True) ∨ (p2 → (p4 → (p3 → False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336315515817622299092623487147 : (p1 → (((p3 ∨ (p3 ∧ (False ∧ p2))) ∨ (p3 → (p4 → ((False ∨ (True ∨ (p4 ∧ ((False ∧ p5) ∨ (p1 ∨ p2))))) → (p5 ∧ p1))))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675399778910923222862595851066 : ((((((p2 ∨ ((((p2 → False) ∨ p1) ∧ False) ∧ False)) → (p5 ∧ ((p2 ∧ p5) ∧ (True → p2)))) → p2) ∧ (p2 → (p3 ∨ (p5 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172901156174406661523302544908 : ((p2 ∧ (((((p1 ∧ (p5 ∨ p2)) → (p2 ∧ (False → p3))) ∨ p2) → p5) → False)) ∨ (((True → p3) ∧ ((False → (p1 ∨ p3)) ∨ p3)) → p3)) := by
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
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216514140116960293944435798373 : ((p5 → (p3 ∧ (p5 → p4))) ∨ (((p1 ∨ (p5 → p3)) → (((p2 ∧ ((((True → False) ∨ p4) ∧ True) → (p4 → p1))) ∨ True) ∧ True)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60250378296198489988069902043 : (((False → False) → ((p4 ∧ ((((p1 ∧ ((((True ∧ p3) ∧ p2) ∧ p1) ∧ ((p1 → (p4 ∨ p1)) → True))) ∨ p2) ∨ p5) ∨ True)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191801912543264299730893127510 : ((p2 ∨ ((((p1 ∨ p4) ∨ False) ∨ p1) ∧ (p5 ∧ False))) ∨ ((False ∧ p3) → ((p3 ∨ (p4 ∧ (False → False))) ∨ (((p1 ∧ p1) → p2) → p2)))) := by
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
theorem thm_5_vars_165027576437565693657355612412 : (((((True → p4) ∧ p2) ∨ (True → ((p4 ∨ ((p4 ∨ (False ∧ p4)) → p3)) ∧ p4))) → False) ∨ (p5 ∨ ((False → p5) ∧ (False → (False ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157183222725042435613746857236 : ((((True ∧ (((p5 ∨ p1) ∨ (p1 → (p3 ∨ p4))) ∨ ((p5 → p2) ∨ (p5 ∧ p1)))) → p1) → p1) ∨ (((p2 ∨ p5) ∨ (p2 ∧ p5)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158504350404259501990641567680 : (((True ∨ p1) → (((p5 ∨ ((p3 ∧ ((p2 → (p1 ∧ p5)) ∧ p3)) ∨ p3)) ∨ (p4 ∨ False)) ∨ p1)) ∨ ((True → p1) → ((False ∨ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171484046950420693214795012739 : (((True → (True → (p4 → (p1 ∧ (p4 → (((p3 → p4) ∨ p3) → False)))))) ∧ p3) ∨ ((((p4 → ((p5 ∨ p2) ∧ p5)) ∧ p4) → True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164704720641590223594707479557 : (((((p5 ∨ p4) ∨ (p3 ∧ ((p1 ∧ (p5 ∨ (p2 ∧ (p3 ∨ p5)))) ∨ p4))) ∨ p3) ∨ p4) ∨ ((((p3 → p2) → p2) ∨ False) → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62729144279945286463124254212 : ((p4 ∧ ((((p5 ∨ ((p4 ∨ p2) → (p1 → p4))) ∨ p1) ∧ ((((p3 ∨ (p4 ∨ p2)) → True) ∧ p3) ∨ (False ∨ p3))) ∧ (p1 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319622783927885660332930247830 : (p4 ∨ ((True → ((p3 ∨ p5) → (True → (p5 ∨ p3)))) ∧ (p4 → (p1 ∨ ((((((True ∧ p5) ∨ p2) ∧ p1) ∨ p4) ∨ p4) ∨ (False → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314694969023234831274264999876 : (p3 ∨ ((p2 ∧ (False ∨ (((p2 ∧ (p1 ∨ True)) ∧ (False ∧ (True → (p3 ∨ p3)))) → False))) → (((True ∧ True) → p1) → (True → (p1 ∧ p2))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (True ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617030150535223473754703482898 : (((((((False ∨ (p2 ∧ p1)) ∧ False) ∨ (p1 ∨ p4)) ∧ (p3 ∧ (True ∨ ((((p3 ∨ (False ∨ False)) → (True → p3)) → p5) ∧ False)))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66523011536626637994939119854 : ((True → ((((p4 ∨ p4) → (p1 ∧ (((((p5 → (p1 → (p5 → p5))) ∨ False) ∧ (p3 → p1)) → p3) → p3))) ∨ (p5 → p1)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135068893741368606618963238831 : ((((((p3 ∨ p2) ∨ p4) ∧ ((p3 ∨ p3) ∨ (p5 ∧ (((p4 → p4) ∨ p3) → p2)))) ∧ (p4 → p3)) ∨ (p2 → p2)) ∨ ((p1 ∧ p1) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199978475118560502646666283949 : ((((p1 ∧ (True → p4)) ∧ p5) → (True ∨ p3)) → (True ∧ ((p4 ∨ p1) → ((p1 ∧ (p2 ∧ ((p3 → p5) → ((True → False) ∨ p4)))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319789684649084912092939663331 : (p4 ∨ (((p5 → True) → ((p4 ∨ p5) ∧ p3)) → (((((((True ∨ p5) ∨ p3) → (False ∨ p5)) → True) ∧ (p5 ∨ p4)) → p5) ∨ (p4 → True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2462772751013726590746432192 : ((((p2 ∨ False) ∧ p2) ∨ (((p2 ∧ p1) ∧ p5) ∨ p1)) ∨ ((p2 → False) → (False ∨ ((p2 → p5) ∧ (False → ((False ∨ p4) → p3)))))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67600515835513022698174391744 : ((p1 → (p1 ∧ ((((True → (p4 → ((((p5 → (p1 ∧ False)) ∨ ((p2 → (False ∧ p4)) → p5)) ∨ p2) → p2))) ∨ p4) ∧ p3) ∨ p1))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253744546795983228664378279792 : ((p1 ∧ p1) → ((p1 ∧ (p5 ∨ ((p3 → (False ∨ p5)) ∨ ((p2 → False) → (False ∨ p5))))) ∨ ((p2 → (((p3 ∧ False) → True) ∨ p4)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671195307289476376061955694450 : ((((p3 ∨ ((((False ∨ p3) → p4) → (p1 ∨ (False → ((p4 ∨ (p3 ∧ p1)) ∧ p4)))) ∧ ((p5 → p2) → p1))) ∨ ((p1 → False) → True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_193988212553036793780501874508 : ((p3 ∨ (False ∧ (p5 ∨ ((p3 ∧ p4) ∨ (p3 ∨ p4))))) → (((p1 ∨ (p1 ∧ (p2 → ((p5 → False) → (p4 ∨ p1))))) ∨ p3) ∨ (True → p1))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259220109184278145821404400636 : ((False → False) → (((True ∧ p1) ∨ False) → ((((p5 ∧ True) ∧ ((p5 → (p1 ∨ (p2 ∨ p3))) ∨ p3)) → p3) ∨ (True ∧ (p2 → (p3 → p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231165830544834336609347383457 : (((p2 ∨ p1) ∨ p4) → (((((p5 ∧ p1) ∧ p4) ∨ (True → ((((p5 ∨ (p3 ∧ p1)) ∨ p4) ∧ p2) ∧ p3))) ∨ (False → (p5 → p5))) ∨ p4)) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h4
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h7
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150227821411238170360168055162 : ((p2 → (p5 ∨ (p3 ∧ (p2 → ((p5 ∨ p3) → (((p1 → True) → p4) ∧ (p3 → (p3 ∨ (p5 ∧ p4))))))))) ∨ ((p1 ∨ p3) → (p1 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136618700726429607416706210992 : ((((False ∨ p2) ∧ p2) → ((((False → (p1 → (p2 → ((False → (True ∨ p4)) ∨ (p2 → False))))) ∧ p5) → p1) ∨ p2)) ∨ (p1 → (True ∧ False))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50789024803860140753789567853 : (((p5 ∨ ((((((p1 ∨ p1) ∨ p1) → ((True ∧ p3) ∧ p5)) ∧ p1) ∧ p1) → (True ∨ (p4 ∧ p4)))) → (((p5 ∨ p2) ∧ p4) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157263316337286937907661570431 : (((((p5 ∨ True) ∨ (p5 → p1)) → (((p4 → p2) ∧ (p2 ∨ (False ∧ (p3 ∨ False)))) ∧ False)) → p3) ∨ (p1 ∧ ((True ∧ p3) ∨ (p3 → False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∨ True) ∨ (p5 → p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247529318995199929394269566199 : ((False ∨ p4) ∨ (((p2 ∧ ((False ∧ (((False ∨ (p1 ∧ p5)) ∨ p2) ∨ (p2 ∧ p1))) → ((False → True) → p2))) ∧ ((p3 ∨ p5) ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171710393439964361933097026794 : (((p5 → (((p4 → (((p1 → p2) ∨ True) ∨ False)) → p1) ∨ (p1 → p1))) ∨ True) ∨ (((((p2 ∨ (True ∨ True)) ∨ True) → p2) → p5) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248218135136925499862633840907 : ((p2 ∨ p1) ∨ ((False ∧ ((p4 ∨ (True → ((True ∨ p2) → ((p4 ∨ p4) → False)))) → p1)) ∨ ((False ∧ p4) → (p1 ∨ ((True → True) ∨ p5))))) := by
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
theorem thm_5_vars_117000217302570422375405181030 : (((False ∨ True) → ((((((((p3 ∧ (p5 ∧ p3)) → False) → (True ∧ p3)) ∧ (p4 → (True ∧ p4))) ∨ True) → p5) → p3) ∨ True)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353698237852077808699267988614 : (p4 → (p5 ∨ (p1 ∨ (((((True ∧ (p3 ∧ p3)) ∧ p3) ∧ True) ∨ p4) ∧ (p5 → ((p3 → p5) ∨ (False → (((p2 → p2) → p3) ∨ p2)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42002420211721895126556189351 : ((((p2 → False) ∧ ((((((False ∨ (p1 ∧ True)) ∨ False) ∧ p3) ∧ (((False ∨ p4) ∧ ((p1 → True) → True)) ∨ p3)) ∨ False) ∨ p4)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306500165114126842111563686360 : (p1 ∨ ((p4 → p2) ∨ ((True ∧ (((((p1 ∨ p2) ∧ (p5 ∧ (((True ∧ True) ∧ False) ∨ p3))) ∨ p5) ∨ True) ∨ p1)) ∨ ((False ∨ p2) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_65036888421791887126099808171 : ((p2 ∨ ((p3 → p3) → (p5 → ((((False ∨ (((False ∨ p4) → p1) → ((p3 ∨ False) ∧ False))) → (p5 ∧ p2)) → (False ∧ p3)) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68014672132681141776346316249 : ((p2 → (True ∧ (((((False ∨ p4) ∨ True) ∧ p4) → (((p4 ∧ True) ∨ p1) ∧ ((True ∨ p2) → ((False ∨ (False ∧ p5)) ∨ p1)))) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42000578236440895656387662617 : ((((p1 → p3) ∧ ((True ∧ (False → p3)) ∧ (((True ∧ (((((False ∨ p5) → p4) → (False ∧ p3)) → False) → p4)) ∧ p2) ∨ p1))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354845461260991961504687721599 : (p5 → (((p4 ∧ p1) ∨ (((True ∨ ((p2 → (p3 ∧ p2)) → p3)) ∧ (True ∨ (p1 → ((True ∨ (p3 ∧ p1)) ∨ p4)))) → (p4 ∧ p1))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325080663076183754486980605429 : (p5 ∨ ((True → False) → (((p2 → (((((True ∧ p2) ∨ p4) ∧ p3) ∨ ((True ∧ p1) ∧ p2)) → True)) → ((p1 ∨ p4) ∧ p5)) ∨ (p3 ∧ False)))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64017072513671468096799564552 : ((False ∨ (((p5 ∧ p5) ∧ ((p3 ∧ ((True ∨ (True → p5)) ∧ True)) ∨ ((False ∧ p4) ∨ ((p1 ∧ p1) → (True → p1))))) ∨ (p3 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261459684146590344141539723411 : ((p5 → p2) → (((p1 → ((p1 ∨ p2) → (True ∨ p1))) → (p2 ∧ p5)) ∨ (p4 ∨ (p2 → (p2 ∨ ((((p1 → p1) ∧ p5) ∧ p5) ∨ p3)))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808825723164016711241327750672 : (((p4 → (p5 → ((p5 ∧ p3) ∨ ((p2 ∨ (p4 ∧ ((((p3 ∧ (True → (p3 ∨ False))) ∧ True) ∧ ((p3 ∨ p5) → True)) ∨ p4))) ∧ True)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185889176268240871506071057564 : ((((False → ((p4 → p2) ∧ (p2 → False))) ∧ (p2 → p5)) ∧ True) → (((((p1 → p4) ∨ p1) ∨ p4) ∧ ((p4 ∨ p1) → p4)) ∨ (False → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810677269150718730680401669418 : (((p5 → (((p1 ∧ p5) ∨ p1) ∨ (p2 → (((((p3 ∧ p3) ∧ (p4 ∧ (p5 → p4))) ∨ ((p2 ∨ p4) ∧ True)) ∨ True) ∧ (True ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110937968291267860626952843726 : (((((((p2 → p1) ∧ p4) ∧ (p1 → (p2 ∨ p5))) ∧ ((((p2 → False) → False) → p5) → (p1 → p1))) ∧ (p5 → p2)) ∧ p2) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41614429736795791325442810921 : ((((p5 ∨ (((p4 → p4) ∧ p2) ∨ (False ∧ p2))) ∨ (((False → p3) → p4) ∨ (((False → (False ∧ p4)) → (p2 ∧ p5)) ∨ True))) ∨ p2) ∨ p4) := by
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
theorem thm_5_vars_186568244896411306382589116835 : (((p2 ∨ ((p2 ∨ p4) ∧ (True ∧ (p5 → p5)))) ∨ (False ∧ p2)) → (((p1 ∨ p5) ∧ ((p1 ∨ True) → (p3 → p3))) ∨ ((p5 → p5) ∧ True))) := by
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h4
      -- One of the premise coincides with the conclusion.
      exact h4
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h7.left
        let h10 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h11
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h7.left
        let h14 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h15
        -- One of the premise coincides with the conclusion.
        exact h15
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352162791098120291091596867738 : (p4 → ((p3 → ((p4 → (p1 ∧ p1)) → False)) → (((((p5 ∨ (p1 ∨ False)) ∧ (p5 ∧ ((True → p1) ∨ p2))) ∧ True) ∧ (p4 ∧ p1)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174491905998874583302013830017 : ((((((p5 → True) ∨ p1) ∨ p1) ∧ p3) ∨ ((p4 ∧ (False ∨ p3)) → (p1 ∨ True))) → (p2 ∨ (p1 ∨ ((p1 → (p1 ∨ p5)) ∨ (p2 ∨ p3))))) := by
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
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358677037570529414495015194070 : (p5 → (p4 → ((True ∨ p5) → (((False ∨ (p3 ∨ (True → (p2 → (((p2 → p1) ∧ (p3 → True)) ∨ ((p3 ∧ p3) ∧ p3)))))) → False) ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260485256481975580512406569294 : ((p3 → False) → ((((((False → p3) ∧ (p3 ∨ (p1 → p2))) ∧ (p3 → p5)) ∨ p4) ∨ p3) ∨ (((p5 ∧ p5) → True) → (True → (p2 → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232046135220996587924128518838 : (((p3 ∨ p4) → False) → (p4 → (p3 → (False ∨ (((p1 ∨ (True ∧ ((p4 ∨ True) ∧ p1))) ∧ False) ∨ (((False ∨ (p4 ∧ True)) ∧ p2) → False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (p3 ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133982088215277762609982816316 : (((((((((p1 → ((p2 ∨ True) → p1)) ∧ ((p1 ∨ False) ∨ p4)) → True) ∧ (False ∧ p1)) → p3) → p1) ∧ False) ∨ False) ∨ (p1 ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216277759415967125050503081571 : ((p2 → ((p4 ∧ p2) ∧ p5)) ∨ ((False ∧ (p3 ∨ (p2 ∧ p1))) ∨ (((True → p1) ∧ (p4 ∨ False)) ∨ (((p1 → (p4 ∨ p1)) → False) → True)))) := by
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
theorem thm_5_vars_118558765522915605630737988912 : ((p3 ∨ (p4 → (p5 → (p2 → (p5 → (p3 ∧ (p2 ∧ (((p1 ∧ (p3 ∨ p4)) ∨ (False ∧ ((p3 → False) ∧ p1))) ∧ p5)))))))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112335070665376837129218634342 : (((p4 → (False ∧ (((((p5 ∨ (False ∨ (p1 ∧ (p2 ∨ (False ∨ p5))))) ∧ True) → ((p3 → p1) ∨ False)) ∧ True) ∨ p2))) ∨ p1) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358739175459563329688978824243 : (p5 → (p5 → (True ∧ (((((p1 ∧ True) ∨ (p3 ∨ True)) ∧ p2) ∧ p3) → ((((((False ∧ True) ∨ (p4 → p5)) ∧ p4) ∨ p5) ∧ p2) ∧ True))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  -- Conjunctions on the left can always be decomposed.
  let h14 := h3.left
  let h15 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- One of the premise coincides with the conclusion.
    exact h17
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h23 =>
      -- One of the premise coincides with the conclusion.
      exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156799158016408297592918019201 : (((p5 ∧ ((((p4 → p4) ∧ ((p4 ∧ p1) ∨ (False ∨ p5))) ∨ (p2 ∨ (p3 ∨ p3))) ∧ False)) ∧ p3) ∨ (False → (p3 ∧ (p1 ∨ (p5 ∧ p1))))) := by
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
theorem thm_5_vars_75793038371437290076710376716 : ((((((p2 ∧ (True ∨ p3)) ∨ p1) ∨ (p1 ∨ ((True ∧ p4) ∨ ((p1 ∨ ((p5 → p4) → ((p3 → p3) ∨ p2))) → True)))) ∨ p3) → False) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p2 ∧ (True ∨ p3)) ∨ p1) ∨ (p1 ∨ ((True ∧ p4) ∨ ((p1 ∨ ((p5 → p4) → ((p3 → p3) ∨ p2))) → True)))) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164700662206235474566374148030 : ((((((p4 ∧ p5) ∨ ((p4 ∧ p2) ∨ p2)) ∨ ((p4 ∧ True) → (True ∨ False))) ∨ p3) ∨ p3) ∨ (((p5 ∧ p1) ∧ (p4 ∨ (p5 ∨ p2))) ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303973465247186202112284995096 : (p1 ∨ ((((p2 ∨ p4) ∨ p5) → ((p2 ∧ p5) ∨ (((((True ∧ p5) ∨ True) ∨ (((False → p4) → p5) ∨ False)) → (p1 ∨ p3)) ∨ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715898869049325979134675059824 : (((((False ∨ (p4 → p3)) ∨ False) ∧ ((p3 ∨ ((((((p3 ∧ ((p4 ∧ p1) → (p2 ∧ False))) ∧ False) ∨ False) → p5) ∨ p5) → p5)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43459533252107688612074177881 : (((((True ∨ p5) ∨ (((True ∧ ((((True → p2) ∨ p3) → (p3 ∨ p2)) ∨ True)) ∨ ((p3 ∧ (True → True)) ∧ p5)) ∧ True)) ∨ p5) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248895661011194256433440031702 : ((p3 ∨ p5) ∨ ((p1 ∨ (p1 ∧ p5)) ∨ (p4 ∨ (p4 ∨ ((False → p2) ∨ ((p3 ∨ ((p2 → (p2 → p5)) ∨ False)) ∧ (False ∧ (p1 → p1)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759549518658071764942991343539 : (((p2 ∧ (((p4 ∧ p5) ∨ ((((p5 → False) ∧ p1) → (p5 ∧ p2)) ∧ ((p3 ∨ False) → False))) ∧ (p4 ∨ (p5 → (p2 → (p3 → p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112769800041042350529593239110 : (((((p3 ∧ p2) → (((p4 ∧ p5) ∧ (p1 ∧ p2)) ∧ False)) → (p1 ∨ (((p5 ∨ ((p3 ∧ p2) → p1)) ∧ p3) ∨ False))) → p2) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301322327932626023493967834995 : (False ∨ (((p5 ∨ (p3 → True)) ∨ p2) ∧ ((((True → (((((p2 ∧ p5) ∨ p4) ∨ p2) → (True ∧ p1)) → p1)) ∨ True) ∨ True) → (False ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_816122571631585690287373692960 : (((((((((True ∧ True) ∧ p3) → ((p3 ∨ True) ∧ False)) ∧ (p4 → ((p2 → p4) ∧ (p5 ∧ (p4 ∧ (False ∧ False)))))) → p3) → p2) ∧ p4) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((((True ∧ True) ∧ p3) → ((p3 ∨ True) ∧ False)) ∧ (p4 → ((p2 → p4) ∧ (p5 ∧ (p4 ∧ (False ∧ False)))))) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- False on the left can always be used.
    apply False.elim h13
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h14 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138351394973401193745529150153 : ((p4 → (((p2 ∧ (((True ∧ (p3 → ((p1 → False) ∧ (True → p5)))) ∧ p4) → ((p4 ∨ p2) ∨ False))) → True) → p2)) ∨ ((False → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49287699862010679833709884190 : (((p5 ∧ ((p2 ∧ (((p4 ∨ (p1 ∨ ((False → p1) ∨ (p5 ∨ p2)))) → p1) ∨ False)) ∧ ((True ∨ False) ∧ p4))) ∨ ((False ∨ True) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87955027110735704315997637328 : (((p4 ∨ (False ∨ ((True → True) ∨ p5))) → ((p1 → (p1 ∧ ((p1 ∧ (p1 → (p4 ∧ p4))) → ((True ∧ p3) ∨ (p1 ∧ p1))))) ∧ False)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ (False ∨ ((True → True) ∨ p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46837249886497264796186536671 : ((((((p2 ∨ ((p4 → p1) ∨ (p5 ∨ p5))) ∨ (p3 ∨ False)) ∨ (((p4 → (False ∧ p5)) → (True ∧ p5)) ∨ p2)) ∧ False) ∨ (p3 ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179370496445552001366089659902 : ((p2 ∨ ((True → True) → (True → ((p5 → p1) → ((p4 ∨ p1) ∨ False))))) ∨ ((p1 ∧ (False ∧ ((p5 ∨ (p5 ∨ False)) ∧ (p1 → False)))) → p2)) := by
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
theorem thm_5_vars_250054812559657914846882325705 : ((True → p3) ∨ ((p5 ∨ p1) → (((((((True ∧ False) ∧ p2) ∨ (True → ((p5 ∧ (p5 ∨ True)) → False))) ∨ p3) ∨ p5) ∨ (True → False)) ∨ True))) := by
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
theorem thm_5_vars_780247962655882672746682937273 : (((p2 ∨ (((((p3 → (p4 ∧ True)) → False) ∨ (False ∨ p3)) ∨ ((True ∧ p2) ∨ (((False ∧ p5) ∧ p5) → True))) → ((False ∧ p4) ∨ True))) ∨ False) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- False on the left can always be used.
        apply False.elim h5
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344777887257520690835784706697 : (p2 → (p4 → ((((((((p5 ∨ p3) ∨ (p1 ∧ (p4 ∨ ((p4 ∨ p1) ∧ p5)))) ∨ p1) ∨ p4) ∨ True) ∨ (p4 ∧ p2)) ∧ (p2 → p3)) → p3))) := by
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
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- Disjunctions on the left can always be decomposed.
            cases h10
            case inl h11 =>
              -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
              have h12 : p2 := by
                -- One of the premise coincides with the conclusion.
                exact h1
              -- We have shown the premise of h5, we can now drive its conclusion.
              let h13 := h5 h12
              -- One of the premise coincides with the conclusion.
              exact h13
            case inr h14 =>
              -- One of the premise coincides with the conclusion.
              exact h14
          case inr h15 =>
            -- Conjunctions on the left can always be decomposed.
            let h16 := h15.left
            let h17 := h15.right
            -- Disjunctions on the left can always be decomposed.
            cases h17
            case inl h18 =>
              -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
              have h19 : p2 := by
                -- One of the premise coincides with the conclusion.
                exact h1
              -- We have shown the premise of h5, we can now drive its conclusion.
              let h20 := h5 h19
              -- One of the premise coincides with the conclusion.
              exact h20
            case inr h21 =>
              -- Conjunctions on the left can always be decomposed.
              let h22 := h21.left
              let h23 := h21.right
              -- Disjunctions on the left can always be decomposed.
              cases h22
              case inl h24 =>
                -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
                have h25 : p2 := by
                  -- One of the premise coincides with the conclusion.
                  exact h1
                -- We have shown the premise of h5, we can now drive its conclusion.
                let h26 := h5 h25
                -- One of the premise coincides with the conclusion.
                exact h26
              case inr h27 =>
                -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
                have h28 : p2 := by
                  -- One of the premise coincides with the conclusion.
                  exact h1
                -- We have shown the premise of h5, we can now drive its conclusion.
                let h29 := h5 h28
                -- One of the premise coincides with the conclusion.
                exact h29
        case inr h30 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h31 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h1
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h32 := h5 h31
          -- One of the premise coincides with the conclusion.
          exact h32
      case inr h33 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h34 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h1
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h35 := h5 h34
        -- One of the premise coincides with the conclusion.
        exact h35
    case inr h36 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h37 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h38 := h5 h37
      -- One of the premise coincides with the conclusion.
      exact h38
  case inr h39 =>
    -- Conjunctions on the left can always be decomposed.
    let h40 := h39.left
    let h41 := h39.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h42 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h43 := h5 h42
    -- One of the premise coincides with the conclusion.
    exact h43



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43554441201758745402584414506 : (((((((((p3 ∧ (p1 ∨ (False → (p1 ∧ False)))) → p4) ∧ p2) ∧ (p1 ∧ ((p5 → (p1 ∧ p2)) ∨ True))) → p5) ∧ p4) → p3) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55220272636530873041314855424 : ((((p2 ∧ (p2 ∨ p5)) ∨ (False ∨ p4)) ∨ ((p3 ∧ (((p3 → p2) → p4) ∧ (p4 → (p5 ∨ ((p4 ∧ p3) → (True ∨ True)))))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595921387489482797882652976183 : (((((((p4 ∧ p3) ∨ True) ∧ (p2 ∧ ((p1 ∧ p4) → p2))) ∨ (((p5 ∨ ((p4 → (False ∧ p2)) ∧ (True ∨ p4))) ∨ False) ∧ p1)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66640849292708000246977802398 : ((True → ((p1 → (((False → (p5 ∧ p1)) ∧ (p2 ∨ False)) → (p5 ∧ p1))) ∨ (((p1 → False) ∧ ((p2 → (True → p4)) → p3)) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310881670796065478883990176478 : (p2 ∨ ((p4 ∨ (p2 ∧ p3)) → (((p1 ∨ (p4 → p1)) → ((p4 ∧ ((p4 → p5) ∧ p3)) → p1)) ∧ ((p1 ∧ ((p4 ∧ p4) → False)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h14 =>
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h15 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h16 := h13 h15
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h20 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h21 := h13 h20
      -- One of the premise coincides with the conclusion.
      exact h21
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756730949492277065781223029183 : (((p1 ∧ (((p2 ∧ (p5 ∨ (p1 ∨ p2))) ∧ (((False → p5) → p5) ∨ p4)) ∨ ((((p5 ∧ True) ∧ ((p5 ∧ p4) ∨ p3)) → p3) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138785514629737485088907253665 : ((((True → p4) ∨ (False ∨ ((((p4 ∨ ((p1 ∧ (True → p2)) → True)) → (p2 → p1)) ∨ False) ∨ (p5 → p1)))) ∧ p4) → (p2 ∨ (p4 ∧ p4))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h3
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h10 =>
          -- False on the left can always be used.
          apply False.elim h10
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h3
        -- One of the premise coincides with the conclusion.
        exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130954930172203165332619480497 : (((((False ∨ False) ∧ p3) → (((p3 ∧ (p1 → p5)) → False) → p4)) → ((p5 → (True ∧ (p1 ∨ p5))) ∧ (True ∨ p1))) ∧ (p2 → (True → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197851709062258692237416697378 : (((p1 → (p3 ∨ False)) ∨ ((p4 ∧ p5) ∧ p3)) ∨ ((p2 → ((False ∧ ((((False ∧ p4) ∧ p5) ∨ True) ∧ p4)) → ((False → p3) ∨ False))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173947632481697539430071367433 : (((((p4 → False) ∧ ((p4 ∧ p1) ∨ (True ∧ p1))) → ((p2 ∨ p4) ∧ True)) → False) → (((True → False) ∨ ((True → (p5 → p5)) ∨ p4)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355868685796537718881600596779 : (p5 → ((((p1 ∧ p3) → p4) ∨ (((((False → (True ∨ p4)) → (p3 ∧ (p2 ∨ p1))) ∧ True) ∧ p1) ∧ (p1 ∧ p1))) ∨ ((p4 → p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59019904258070338719745794003 : (((p3 ∧ p5) ∨ (((((p4 ∨ p4) → (((p4 ∨ p1) ∧ (p5 ∨ p1)) ∧ (True ∨ p2))) → p2) ∧ ((p3 ∧ p5) ∧ p4)) → (p1 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216277608187333945097946083060 : ((p2 → ((p4 ∧ False) ∧ p5)) ∨ (((p4 ∧ (((True → False) ∧ (p3 → (p1 → p2))) ∨ p1)) ∧ p3) ∨ (((False ∨ (p1 → True)) ∧ p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310261252136066796500327307548 : (p2 ∨ (((((True ∧ p4) → ((True → p3) ∨ p4)) ∨ True) ∨ p5) ∧ (p5 → ((p4 ∨ p4) → ((p1 ∧ False) ∨ (False → (False ∨ (p5 ∨ p2)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354369116048290974478136393006 : (p5 → ((((p2 ∧ p4) ∧ (p4 ∧ (True ∧ p4))) ∨ (p4 ∨ ((True ∨ ((p5 ∧ p2) ∨ ((p4 → p3) → ((False ∧ p2) ∧ p5)))) ∧ p5))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302804135172199916370746583204 : (False ∨ (p5 ∨ ((p1 → ((p1 ∨ (p4 → p5)) → ((((p3 ∧ p2) → p4) → p4) → (True → (p3 → (((p5 ∧ p2) ∧ p2) → p4)))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40341601320072445345988215768 : (((((True ∧ ((p3 → p4) ∧ (((p5 ∧ True) ∨ ((p4 ∨ p1) → (((p2 → (p5 ∧ p5)) ∨ p2) ∨ p5))) ∧ p4))) ∨ True) ∨ p3) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



