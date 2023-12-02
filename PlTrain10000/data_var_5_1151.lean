variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115770842019344527503286405736 : (((p1 → (p4 ∨ (p1 → (p3 → False)))) → (((True → (False ∧ (p1 → (p2 ∧ (p3 ∨ p2))))) ∧ p4) ∧ (False → (False ∨ p4)))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227640399587206104893039732814 : ((False ∧ (p4 ∨ p4)) ∨ (((((False ∧ p1) ∧ ((p5 ∧ True) ∧ p5)) → p1) → (p5 ∨ (p3 ∨ False))) → (p3 ∨ (p5 ∨ ((p2 ∧ p4) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60101734199458973281023707996 : (((p3 ∨ p1) → (True ∧ (True → (p1 → (((p2 ∧ p5) → True) → (((p4 → (((p2 ∧ p2) ∨ (p2 → True)) ∧ p5)) ∧ p2) ∨ p1)))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343234554858408389704784049220 : (p2 → ((p5 ∧ (p1 → p5)) → (False ∨ (p3 ∨ ((p4 ∧ p3) ∨ ((p4 ∨ (p1 ∨ True)) ∧ (p3 ∨ (False → ((True ∧ p1) ∨ (p3 → True)))))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307130335950926268188480119341 : (p1 ∨ (False ∨ (((((p3 ∨ p3) ∨ False) → (False ∧ p1)) ∨ ((((((p5 ∨ True) → True) ∧ True) ∨ False) → (p3 ∨ p2)) ∨ True)) ∧ (p3 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762130409390917411673512359886 : (((p3 ∧ (((((p3 → (((True ∨ True) → (p1 ∨ (True ∨ p4))) ∨ ((True ∨ p4) ∧ p1))) ∨ (p2 ∨ True)) ∧ p3) ∧ True) ∨ (p5 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158946436730310753020387322881 : ((p2 ∨ (((True ∧ p3) ∨ (p4 ∨ (p1 → p3))) ∧ (((p3 ∨ p4) ∧ (True ∧ p4)) → (False ∨ p4)))) ∨ (True ∨ ((True → (False ∨ False)) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180571726618716136335195292147 : (((((p5 ∧ False) → (False ∧ p4)) ∨ (p4 ∧ p3)) → ((p3 → False) ∧ p5)) → (((p2 → (((p2 → p4) ∨ p3) ∧ p5)) ∧ (p3 ∨ False)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∧ False) → (False ∧ p4)) ∨ (p4 ∧ p3)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141275430747498608072581043345 : ((((p3 → (False ∨ True)) ∨ p3) ∧ (p4 → ((((p4 → p2) ∨ (p2 ∨ p3)) ∨ ((p2 → (p2 ∨ False)) ∧ p5)) → p5))) → ((p2 ∨ p5) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665318494525188311999796198139 : (((((((p3 ∨ True) ∨ p3) ∨ (p4 ∨ (p5 ∨ (((True ∧ (True ∧ (p1 ∧ p2))) → p5) ∨ (p3 → p1))))) ∧ p2) ∧ ((p5 ∧ False) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165203343739089030220010499909 : ((((((((True ∨ (p4 ∨ p4)) → True) → p5) → (p2 → False)) ∨ p4) → False) ∨ (p2 ∧ p3)) ∨ (((p2 ∧ False) → (p2 ∧ False)) ∨ (False ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187188887439689979986077028232 : (((True ∨ True) → ((p1 ∧ (((p1 ∧ p2) → p4) → p1)) → p3)) → ((((((p1 → (p2 → False)) → p5) ∧ p5) ∨ True) ∨ (p1 ∧ p5)) ∨ p5)) := by
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
theorem thm_5_vars_329104511348376637564620979500 : (True → ((((p4 ∧ p2) → p3) ∨ p4) ∨ (((p5 ∧ (True → (p5 ∧ (False ∨ False)))) ∨ True) ∨ (p3 ∧ (p5 ∧ (((p1 ∨ False) ∨ False) → p2)))))) := by
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
theorem thm_5_vars_237956158245788373374537200002 : ((True ∨ False) ∧ ((p4 ∧ ((False ∧ ((p1 ∨ p5) ∨ ((False ∨ p3) ∧ False))) ∧ False)) ∨ (((False → p3) ∧ (True → ((p1 ∧ p2) ∧ p5))) → p5))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626686729570803010052834414202 : ((((p5 → (((p3 ∨ p5) ∧ ((p4 ∧ (p2 → (p2 → (((p2 ∨ p5) → True) → ((p3 ∨ p4) ∧ (True ∧ False)))))) ∧ p1)) ∧ False)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_327872566111567261956283142550 : (True → (((p4 → p5) → (True ∧ ((((((((p3 ∨ ((p5 ∧ p2) ∨ p2)) ∨ p2) ∨ p5) ∧ p4) ∧ True) → p3) ∨ p4) ∧ False))) ∨ (False → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962497082352976848228605283551 : ((((True → p2) ∧ ((False ∧ p3) → (p3 ∨ (p5 → (((True ∧ p1) ∨ (((p1 ∨ ((p1 ∧ False) ∨ p2)) ∧ p3) → (p3 ∨ p4))) ∧ p2))))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196680088383230992222870867922 : (((((p4 → (p5 ∨ p1)) ∧ p4) ∨ p3) ∧ True) ∨ ((((p5 → (p4 ∧ (p5 → False))) ∧ False) ∨ True) ∨ ((p2 ∧ (p1 ∨ (p2 ∧ p5))) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264584246808666763791740733680 : (True ∧ ((p3 ∨ (p5 ∨ p3)) ∨ ((p2 ∧ (((p4 ∧ p3) ∨ True) → p1)) ∨ ((p1 → (p4 ∨ (True ∨ ((p2 ∧ p5) ∧ (p1 → True))))) ∧ True)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1821866593281155454368226207 : ((p4 → (((p1 ∨ (p4 ∨ ((p3 → True) ∨ True))) → (((True ∧ (p4 ∨ p1)) ∧ True) → p5)) ∧ (p4 ∧ False))) ∨ ((p5 ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150162565562144525965467301051 : ((p1 → (((((p3 ∨ (p1 → p1)) ∨ p2) ∧ True) ∧ p3) → ((p4 ∧ ((p5 ∨ False) → p2)) ∧ (p2 ∧ p4)))) ∨ (p2 → (True ∨ (p2 ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185189730899296825912161033873 : ((True ∧ (((p3 ∨ (p2 ∧ ((False → p4) ∧ True))) → p4) ∨ p2)) ∨ (p2 ∨ ((p1 ∧ (p1 → (p4 ∧ (p4 ∧ (p4 → (False ∧ p3)))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606157484844160925872193696755 : ((((((((p4 ∧ (((p2 → (False ∨ p3)) → p4) → p1)) ∧ ((((p4 → p2) ∧ p2) ∨ p1) → (p2 → p1))) → p3) ∧ p3) ∧ True) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260310478120299166205979522755 : ((p2 → p4) → ((p3 ∧ (False ∧ (p2 ∨ p2))) ∨ (((p4 → ((p3 ∨ p3) ∨ p4)) → (p4 → (False ∧ p4))) → (((False ∨ p4) ∧ True) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (p4 → ((p3 ∨ p3) ∨ p4)) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h8
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779001646294698266473425255675 : (((p1 ∨ (p3 → (p4 → (p5 ∨ ((p1 ∨ ((True ∨ (p3 ∨ True)) ∧ (p2 ∧ (((((p1 ∧ True) → p4) ∧ p2) → False) ∨ False)))) ∨ True))))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177979696348599576745650774075 : (((p1 ∧ (p3 ∨ (((p1 ∨ p3) → (p3 ∧ p2)) ∨ (False ∧ False)))) ∨ p4) ∨ ((False ∧ p1) → (p2 → (((p4 ∧ (p4 → p3)) → p1) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165002105795470926618633952716 : (((((((p4 ∨ True) ∧ p1) ∨ p4) → (p3 ∨ p4)) → (False ∨ (False ∧ (True ∨ True)))) → False) ∨ (((p2 ∧ p1) → True) ∨ ((p4 ∨ p1) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_394858254338913474099839465449 : ((((True ∧ (False ∨ (((((True → ((p1 ∨ (p2 ∧ (p1 → True))) → p5)) → (False → p1)) ∨ p5) → ((p5 ∧ p5) → p2)) ∨ p2))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_165147517973045571076067531780 : (((((p4 ∧ (True ∨ p3)) → (((p1 ∧ p2) → p2) ∨ p2)) → (p2 ∨ True)) ∧ (p4 ∧ p1)) ∨ (p1 → ((p5 ∧ False) ∨ (p1 ∧ (p1 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179414745758196751123734397957 : ((p4 ∨ ((p5 ∨ (p5 → ((p1 ∧ (p2 ∨ p2)) ∧ (p3 ∨ p5)))) ∨ True)) ∨ (p3 → ((True ∨ p5) ∨ ((p1 ∧ ((p2 → p1) ∧ p4)) → True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164493442726148319940603931289 : ((((((((p4 ∧ False) → p5) ∨ (True ∧ p5)) → (True → p4)) → (True ∨ False)) → p1) ∧ True) ∨ (((True ∨ p1) ∨ (p1 ∨ (p3 ∨ p1))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340880038397326739532572874401 : (p2 → (((((p1 ∧ ((p4 ∧ ((True → p2) ∨ p5)) ∧ True)) ∨ (p2 → p1)) ∧ (p5 ∧ True)) → ((True → False) ∨ (p5 ∨ (p5 → False)))) ∨ p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h4.left
      let h14 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h4.left
      let h17 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h4.left
    let h20 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198414958798631292378968500006 : ((p4 ∧ ((p5 → (p5 ∨ (p3 → p1))) → p5)) ∨ (((p1 ∨ ((True ∧ (p2 ∨ p2)) → p1)) → p4) → (p2 → ((p2 ∨ (p2 ∨ p2)) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129297446029157741318877838400 : ((((False ∧ (False → False)) ∨ (((p3 ∧ (p4 → ((p4 ∧ p4) ∧ False))) ∨ p5) → ((p3 → p3) → (True ∧ False)))) ∨ True) ∧ ((p1 → p1) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624845082850457772115529977246 : ((((p5 ∨ (((p2 ∨ ((p1 ∨ (p4 ∨ ((False → ((True ∨ p2) ∧ True)) → (p1 ∧ p1)))) → p3)) ∨ p2) ∨ (p3 → (p4 ∧ p2)))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326300620431227131800799663464 : (p5 ∨ (p4 → ((((False ∨ p5) ∨ (((((p4 → p5) → p5) ∨ False) ∨ p1) → True)) ∨ p3) ∧ ((p1 ∨ p4) ∧ (True → ((p1 ∨ p4) ∧ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715249012742770464743824246606 : ((((p1 → (p1 → (p5 ∨ (p5 ∧ p4)))) → (p3 ∨ (((p3 → p1) → (p2 ∨ p2)) → ((p3 → p4) ∨ (((False → False) ∧ p3) → True))))) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44380630677067776741996352790 : ((((((p3 ∨ (p2 → (p1 ∨ ((p2 → (p1 → p4)) ∧ p2)))) → False) ∨ False) ∨ ((p3 ∨ ((p2 → p1) ∧ (p1 ∧ p2))) → p4)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340726773432807368179961532340 : (p2 → (((p3 → (p1 ∨ (True → (((p3 ∧ p4) → p1) ∨ ((p2 ∨ ((p4 → (p3 ∧ p4)) ∨ (p4 ∨ (p3 ∧ p4)))) → p1))))) ∧ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320132296888676418866399305737 : (p4 ∨ ((False → (False ∧ True)) → ((True ∧ ((p5 ∨ (p5 → p4)) → p1)) ∨ (True ∨ ((True → p3) → (p2 ∨ ((p1 ∧ p2) ∧ (p2 → p5)))))))) := by
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
theorem thm_5_vars_19764470309207190538434767577 : ((((p3 ∨ ((p1 ∧ ((False → False) ∨ (True → ((False ∨ False) ∧ p1)))) ∧ False)) → p1) → ((p5 → ((False ∧ (p3 ∧ True)) ∨ False)) ∨ True)) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357499503094596986827796574832 : (p5 → (True ∧ ((((False ∨ (((False ∧ (p3 ∧ p3)) ∧ p3) ∨ p2)) ∨ p3) ∨ (((p4 → (p2 → p1)) → (p2 → p4)) ∧ p3)) ∨ (p1 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606746248299831951333664905235 : ((((((p4 ∧ ((((p3 → (p2 → ((False ∧ True) → p3))) ∧ False) ∨ True) → (((p2 ∧ p1) ∧ p1) ∧ False))) ∨ (p4 ∨ p1)) ∧ p3) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_135908501352951182892456554760 : ((((p3 ∨ (p1 ∨ ((p4 ∨ p5) ∨ p2))) ∧ ((p3 ∧ False) ∨ p3)) → ((p4 → (p5 → False)) ∧ ((False ∧ p4) ∧ p4))) ∨ ((p5 → p5) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55490426807841310103673200238 : (((((p4 ∨ p3) ∨ p5) → (False ∨ p2)) → ((p1 ∨ (((p4 ∧ False) ∧ p5) ∧ False)) ∨ (True → (p4 ∨ (((p5 ∧ p1) ∧ p1) → True))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184250366811635325092996681598 : ((((False ∨ ((p2 ∨ p1) → ((p2 → p4) → p3))) → p1) → p5) ∨ ((((p1 ∧ p3) → p2) → p1) ∨ (p1 ∨ ((p4 ∧ False) ∨ (p5 → True))))) := by
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
theorem thm_5_vars_82962639952204648932501586714 : ((((((p4 ∧ p1) → (((p5 → True) ∨ ((False → p4) ∨ True)) → False)) ∨ (p3 ∨ True)) ∨ (p5 ∨ False)) → (False ∧ ((p4 ∨ p2) ∨ p1))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p4 ∧ p1) → (((p5 → True) ∨ ((False → p4) ∨ True)) → False)) ∨ (p3 ∨ True)) ∨ (p5 ∨ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337520602832945044691324254213 : (p1 → ((((((p2 → (p2 ∧ False)) → p2) ∧ ((p5 ∨ p5) → (p4 ∧ (p4 ∨ (p2 ∨ True))))) → False) ∨ p1) ∨ (p4 ∧ (True ∧ (p1 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156732312969170207361416348675 : (((((p1 → (p3 ∨ p5)) ∨ False) ∧ ((p1 → (p3 → ((p4 → p4) → p4))) ∨ (p3 ∨ False))) ∧ p3) ∨ ((False → p4) ∧ ((p1 → True) → True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54338700302932627437366074123 : (((p5 ∧ ((p1 ∨ (p5 ∨ p5)) → (False → False))) ∧ (p4 → (p2 ∧ ((p3 → ((True → ((p5 ∧ (p4 → p2)) → p5)) ∧ True)) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243775145006871573165026549483 : ((p5 → p5) ∧ (((((((p4 ∨ p4) ∧ (p1 → (p4 ∧ (p1 ∧ (p4 ∧ (p5 ∨ False)))))) ∧ p5) ∨ (True ∨ p2)) → p2) → p2) ∨ (p3 ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((((p4 ∨ p4) ∧ (p1 → (p4 ∧ (p1 ∧ (p4 ∧ (p5 ∨ False)))))) ∧ p5) ∨ (True ∨ p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134157685958521494467862535612 : (((((((True ∨ False) → ((p3 ∨ p3) ∧ (p5 → p5))) → (p1 ∧ p4)) ∧ (p4 ∨ True)) → ((False ∨ p3) ∧ p1)) ∨ True) ∨ (p5 → (p2 ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55436012195729011650948723819 : ((((((p3 ∧ False) ∨ False) ∨ p3) → p4) → ((p3 → (((p2 ∨ p2) ∨ ((((p3 ∧ True) → True) ∨ (p2 ∧ p3)) → p4)) ∨ p2)) ∨ p5)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : (((p3 ∧ False) ∨ False) ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h10 : (((p3 ∧ False) ∨ False) ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h10
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68974851790175096546742169089 : ((p4 → (p4 → ((True ∨ p2) → ((p3 ∧ (p2 → p2)) ∨ ((p3 ∧ ((p2 ∨ (False ∨ p5)) ∨ ((p1 ∨ True) ∨ (p5 → p1)))) ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175091236253751163935454894657 : ((p3 ∧ (False ∨ ((False → ((True ∧ ((False → (p4 ∨ p1)) ∨ True)) ∧ p5)) ∧ p4))) → ((p2 → False) ∨ (False ∨ (p5 → (p2 → (False → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199360034592549763766461278897 : (((((p3 ∨ p3) → p3) ∧ (p2 ∨ p2)) ∨ p3) → ((((p3 ∧ p1) ∨ p3) ∨ p1) ∨ (p4 ∨ ((p5 ∧ p4) ∨ ((False ∨ False) → (p3 ∧ False)))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h15 =>
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16
  case inr h17 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66485820223401395213161592196 : ((True → ((((p5 ∨ (((p3 ∨ p4) → (False → (p3 ∨ (False ∨ True)))) → p2)) ∧ ((p5 ∨ p5) ∨ p2)) ∨ ((p1 ∧ p1) → p1)) ∨ p5)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748455421477219765148498375409 : ((((p2 → p4) → (p2 → (((((False ∧ p2) → p5) ∧ False) ∧ (((p3 ∨ (p1 ∨ (False ∧ p5))) ∧ (p1 ∨ p1)) ∧ (p5 → True))) ∨ p4))) ∨ p3) ∧ True) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164041922532494166448984413130 : ((False ∨ (True ∧ (True → (((p5 ∧ (p1 → (False ∨ (p5 → p5)))) ∨ p3) → (p4 ∨ True))))) ∧ (((False ∧ p2) ∧ True) ∨ ((True ∧ p2) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798159436343185335212131491468 : (((p1 → (((((p5 → False) ∨ ((p1 ∨ True) → (True ∨ (p5 ∨ (p1 ∨ False))))) ∧ (p4 → p5)) ∨ p2) ∨ ((p5 ∨ p2) ∨ (p3 → p3)))) ∨ p3) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197508084327988131181192108153 : (((p4 ∨ ((p1 → p3) → p5)) ∧ (p2 ∨ p5)) ∨ ((((p5 ∧ True) → p3) ∧ p5) → ((p1 → p4) → ((p3 ∧ p3) ∨ (p4 ∧ (True ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p5 ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h6
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : (p5 ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148355782998897446035846331856 : (((p4 ∧ (p2 ∨ (False ∧ (False ∧ (True ∨ ((p1 ∨ p1) ∨ (p5 ∨ p3))))))) ∧ ((True ∨ (p4 ∨ False)) → p2)) ∨ (p3 → (p5 → (False ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306155963932968906552357551397 : (p1 ∨ (((False ∨ p5) ∨ p1) ∨ ((p4 ∨ p4) ∨ ((((((p1 ∨ p4) ∧ ((p4 → p3) → (p3 ∨ False))) ∨ p5) ∨ (False → p2)) ∨ True) ∨ p1)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264269285743315002407320077854 : (True ∧ ((((p5 → True) ∨ p3) → (False ∨ p2)) ∨ (((p2 ∨ (((False ∨ p2) → (p5 ∧ p3)) → (True ∧ (p1 → p3)))) → p1) → (True ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61230232493482643778873361788 : ((False ∧ (p2 ∧ ((((p5 → ((True → p4) → ((False ∧ False) → False))) → (p5 ∨ ((p1 ∧ p2) ∨ p2))) ∧ ((p2 ∨ False) → p5)) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213435362593730102619951035807 : (((p4 ∨ (True ∨ p3)) ∧ p3) ∨ (((((p2 ∨ False) → p1) ∧ p3) ∧ (p1 → (p1 ∧ (True → p4)))) ∨ (((p1 ∧ (p4 → p2)) ∧ False) → p4))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337335211381475982160270395772 : (p1 → ((p5 → ((((((p2 → (p3 ∧ True)) → (p1 → ((p3 ∨ (p5 ∧ p3)) ∧ p3))) ∧ p1) ∨ p1) ∨ False) ∧ p1)) ∧ (p4 ∨ (False → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117875598766082436763929865841 : ((p5 ∧ ((((p3 ∧ False) ∨ (((p1 → (((p3 ∨ p5) ∨ ((p5 ∧ p5) → p4)) ∨ (False ∨ p5))) → p2) ∨ True)) ∨ p5) → False)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208186016165121602453352527978 : (((p1 ∨ (True ∨ False)) → (True ∧ False)) → ((p5 ∧ ((((p2 → True) → p4) ∧ p1) ∧ (p3 → p5))) ∧ (((p4 → p4) → (p3 ∧ p2)) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ (True ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (p1 ∨ (True ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : (p1 ∨ (True ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h13 : (p1 ∨ (True ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h14 := h1 h13
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- False on the left can always be used.
  apply False.elim h15
  -- Implications on the right can always be decomposed.
  intro h16
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h17 : (p1 ∨ (True ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h18 := h1 h17
  -- We need to get the right conjuct of h18 based on <expert-advice>.
  let h19 := h18.right
  -- False on the left can always be used.
  apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354639736159207150069806222400 : (p5 → ((((True → ((p1 ∧ (p5 ∨ (((((p4 → p2) ∨ p3) → p1) ∧ (True ∧ p4)) → ((False ∨ p5) ∨ p1)))) ∧ p4)) ∧ p5) → p2) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47354606725238234201206928872 : ((((p2 ∧ False) ∨ ((((p4 ∧ p5) ∧ ((((((p4 ∧ p2) ∧ p3) ∧ False) ∨ p3) → True) ∨ (p4 ∧ p1))) ∧ False) ∨ True)) ∨ (p2 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40841201234816440640027217925 : ((((p4 → ((p4 ∧ ((True ∨ p1) → (((True → (p1 ∨ (True ∧ (p4 ∨ ((True → p2) ∧ p2))))) → p1) ∧ p5))) ∧ p3)) → p4) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314022954938307701226380631059 : (p3 ∨ ((p4 ∨ ((p4 ∨ ((p3 → p5) → ((p2 ∨ (p4 ∨ (False ∨ ((p5 ∧ p2) ∧ False)))) → (p5 → p4)))) ∧ (p2 ∧ p3))) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61410369614382163057668815207 : ((p1 ∧ ((((p3 ∨ ((p3 ∨ (p1 ∨ ((p4 ∨ True) → ((p5 ∧ (False ∨ p2)) ∨ p5)))) → p1)) ∨ (True → (p5 → p5))) ∧ p1) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140593510148604414505009702814 : ((((p2 → (p1 ∧ (((p2 → (p2 → (False ∧ p3))) → (p5 ∧ p2)) ∧ False))) ∨ True) → (((p1 ∨ p3) → p3) → True)) → ((p4 ∧ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52012901625346886857860035440 : (((p4 ∧ ((p2 ∨ ((True ∨ p2) ∧ p2)) ∨ ((False ∧ p2) ∧ (False → (True ∨ p2))))) ∨ (p1 → ((p5 ∧ p2) ∨ ((p5 ∨ False) ∨ p1)))) ∨ p1) := by
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
theorem thm_5_vars_231899110779133389095650238369 : (((False ∨ True) → True) → (p3 → ((((((p2 → False) → p2) ∨ False) ∨ ((False → ((p5 → p4) → False)) ∨ ((p4 ∨ p1) ∧ False))) ∧ True) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84374713432975630798791848394 : (((p4 ∧ ((True ∨ p3) → (((p3 → True) ∨ p1) ∧ (((p3 ∨ p2) → False) ∧ False)))) ∨ ((p1 ∨ p5) ∧ ((p1 ∧ p4) ∧ (p5 ∧ False)))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (True ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h14.left
      let h18 := h14.right
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h11.left
      let h21 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h20.left
      let h23 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h21.left
      let h25 := h21.right
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40564779016629541692830188937 : ((((p3 → (False ∨ (((p2 → p5) ∨ (p3 ∨ p1)) ∧ ((p1 ∧ (False ∨ ((p2 ∧ p2) ∨ p4))) ∧ ((p5 ∨ p3) → p1))))) ∨ p5) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763589426700583195862473195781 : (((p3 ∧ (p4 ∧ (((False → (p5 ∧ True)) → ((True ∧ ((True ∧ ((True → False) ∧ False)) ∨ p4)) → False)) → (p5 → ((p1 → p1) ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191276560292302045119096429826 : (((p2 ∨ p1) ∧ (p4 ∧ (p4 ∨ (p4 ∧ (True ∨ p4))))) ∨ ((((p3 → True) ∧ (p2 ∧ False)) → (p4 → ((p5 → p1) ∨ p5))) ∨ (p3 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46229267153971712774784718184 : (((((((p3 → (p1 ∨ p1)) → ((p5 → p5) ∧ ((False ∨ True) ∧ (p4 ∨ p5)))) → (p2 ∨ p2)) ∨ p4) ∨ (p5 ∨ p3)) ∧ (True ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185630772709562068426961374520 : ((True → (p2 ∨ ((((p3 → False) ∧ p1) ∨ False) ∨ (p3 ∨ False)))) ∨ ((p5 ∧ (p5 ∧ p1)) → ((p4 ∨ (p4 ∨ p4)) ∨ (p2 → (p5 → p1))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57924810403403688742946470013 : (((True → (p2 ∧ p1)) → (((False ∨ (p1 ∧ p1)) ∨ False) ∧ ((p5 ∨ p3) ∨ (p2 ∨ (((p5 ∨ (p5 ∧ (p4 ∨ p4))) ∧ p4) → False))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9920879393937973479893718739 : (((p1 ∧ (False ∨ ((((((p5 ∧ p5) → p4) → (p3 → ((p5 → p1) ∧ p3))) ∨ (p1 ∧ (p3 ∧ p4))) ∨ (p4 ∧ p3)) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134424069933498822490290148857 : (((p4 → ((((p3 ∧ (p4 ∧ (p2 ∧ True))) ∧ ((p3 → (p1 → p4)) → (True → p5))) ∧ (False ∨ p5)) ∨ p3)) ∨ True) ∨ ((False ∧ False) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136483870700762518439753267134 : ((((p4 ∨ False) ∨ p3) ∧ ((False ∨ ((p3 ∧ (((False → p2) ∨ (p3 ∨ (p4 ∧ (p1 ∧ p4)))) ∨ p3)) → False)) → p2)) ∨ (p5 → (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614681107630120731436577315282 : (((((((((p3 → (p5 ∨ (p5 ∧ p2))) ∧ ((True ∧ p1) → p5)) ∧ (True ∨ p5)) → p5) ∨ p1) ∨ (p1 → ((p3 → p2) → p3))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135425701470087668983951530026 : (((p5 ∧ ((p4 ∧ (True → (p5 → True))) ∧ (True ∨ (p1 → (True ∨ ((p4 ∧ p5) ∨ p3)))))) ∨ (p1 ∧ (False ∧ p3))) ∨ (True → (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243021888762622859720639922411 : ((p4 → True) ∧ (p5 ∨ (p3 ∨ (((True → (((False ∨ True) ∧ (((p4 ∧ p4) ∧ p2) → p3)) → p1)) ∨ (p5 → (False → p5))) ∨ (p4 → p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636828715897045112480285672972 : (((((((((p4 ∧ p3) ∨ p3) → (p5 ∨ p4)) → p1) ∨ (p2 ∨ (True → p2))) → (p3 ∨ (p4 ∧ ((p4 ∨ True) ∧ (p3 ∨ True))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780694391823948939487795091223 : (((p2 ∨ ((False ∨ (p1 → ((p5 ∧ p3) ∨ (False ∧ p1)))) → (True → ((((p2 ∧ False) ∨ (((True ∨ p4) → True) ∧ p4)) ∨ p1) ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39426333177848143933143425009 : (((p4 ∧ (p3 ∨ ((p5 ∨ (p4 ∧ p1)) → (p4 ∧ (p5 ∧ (((p1 ∨ p5) → False) ∧ ((p1 ∧ p3) ∨ (p2 → (p5 ∧ False))))))))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136846554281491317948708400636 : (((p3 ∧ p1) ∨ ((p1 ∨ p5) → ((p1 ∧ p4) ∨ (((p5 ∨ p1) ∨ ((False → (True ∧ p2)) → (True ∨ p1))) ∨ p5)))) ∨ ((p2 ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161178784750058526391814880314 : (((False ∨ True) ∨ (p1 → (((p3 ∧ (p5 ∨ (p5 → (p3 ∨ p3)))) ∨ (True ∨ p1)) ∨ (p2 → p2)))) → ((p5 ∨ (False ∨ (p5 ∨ True))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
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
theorem thm_5_vars_42357217752241772178373847146 : (((p3 ∧ (False ∧ ((((p3 ∨ p3) → ((((p5 ∨ p4) → True) ∨ False) ∧ p1)) ∨ (p3 ∧ ((p5 ∧ (True → p3)) ∨ True))) ∨ p1))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658464826911183465514833379433 : ((((p1 ∨ ((((True ∧ True) ∨ True) → (p4 → False)) → ((p4 ∨ p4) ∧ ((p3 → ((p5 ∨ False) ∧ True)) ∨ (True → p5))))) ∨ (False → False)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_43935100951204375183404178003 : ((((((p2 ∨ (p3 ∨ p1)) ∨ (False ∨ (p5 ∨ ((p4 ∨ (p3 → p5)) ∨ p1)))) → ((p3 ∧ p1) ∨ (p1 ∧ p2))) ∨ (p2 ∧ p4)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119585480014531325830939665216 : ((p5 → ((p3 ∨ False) ∨ (((True ∨ (p5 → (False → (False → True)))) → p4) ∧ (p4 → ((p5 → (p2 ∧ (p1 ∨ p2))) ∧ p1))))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183831955991522189525900222326 : ((((p5 ∨ (((p3 ∧ (p2 ∧ p2)) ∨ p1) → p3)) → p2) ∧ True) ∨ (p2 → ((p2 ∨ p4) ∨ ((True ∧ p3) ∧ (p2 ∨ (True ∨ (p2 → p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



