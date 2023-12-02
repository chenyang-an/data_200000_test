variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41298955529749994964580403094 : ((((p1 ∨ ((p4 → (p2 ∨ ((p5 → ((p2 ∨ (p4 ∨ (p4 ∧ False))) → p1)) ∨ True))) → p2)) → ((p3 → p5) ∨ (False → True))) ∨ p1) ∨ p5) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303932975976940670848936402640 : (p1 ∨ (((((p5 ∨ p3) ∧ ((p4 → p3) ∧ p5)) → p1) → ((p2 ∨ (((p5 ∧ ((p2 ∧ True) → (False → p1))) ∨ p3) ∨ p3)) ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354764975125817931971871992501 : (p5 → ((((((p4 ∧ p4) ∧ (p4 ∨ (p1 ∨ False))) → (False → p1)) → p1) ∨ ((p5 → (p2 ∧ (((p5 → p5) ∨ False) ∧ p3))) ∨ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49178405780347279448038159278 : ((((((p5 ∨ p2) ∧ p4) ∧ False) ∨ (p1 ∨ (False → (p4 → ((p1 ∧ (p4 → p5)) → (p3 → (p5 → True))))))) ∨ ((p2 ∧ p1) ∧ p3)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686145870514384604185785178563 : ((((((p5 ∧ (p3 ∧ (False ∧ (p1 ∨ (p3 ∨ False))))) ∨ (False ∧ p5)) → (p1 ∨ (p3 ∨ True))) → (False ∧ (p1 ∧ (True → (False ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47407969373006657749558196128 : (((False ∧ ((p1 → ((((False → (p1 ∧ p4)) ∨ p3) → True) → (((((p5 ∧ p4) ∨ p4) → p3) ∨ p4) ∧ p3))) ∨ p5)) ∨ (p4 → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249536928670734307643699378016 : ((p5 ∨ p2) ∨ ((p5 → (p3 ∨ ((p3 → p3) → ((p4 → ((p2 ∧ ((p3 ∧ p3) ∧ p3)) ∨ False)) ∨ (p2 → ((True → p5) ∨ p2)))))) ∨ p2)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135281735533973234343824566620 : (((False → (False ∧ (p1 ∨ (((((True ∨ p3) ∨ p1) ∨ (p5 → p2)) ∨ ((p2 ∨ p2) ∨ p3)) → False)))) → (True ∧ p3)) ∨ (True ∨ (p1 ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244625053435391039916395612092 : ((False ∧ p5) ∨ ((((((p5 ∧ p1) ∧ p5) ∧ (((True ∨ (p1 ∧ (p1 ∧ (p4 ∧ (p1 ∨ False))))) ∨ p5) ∧ p2)) ∨ p2) ∧ False) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38363276346750580201337141668 : (((((((True ∧ (p5 → (p2 ∧ p3))) → p4) ∧ (p5 ∨ False)) ∧ (p4 ∧ (False ∧ p5))) ∨ (((p4 ∧ (p3 ∨ p2)) ∨ p3) → True)) ∧ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119486409341673906780766231751 : ((p4 → (p1 ∨ ((p3 ∨ (p2 ∨ ((p4 ∧ (p1 ∧ (((p2 → p2) ∧ p5) ∧ (((p4 ∨ p4) → p4) → True)))) ∨ True))) ∨ True))) ∨ (False ∨ p1)) := by
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
theorem thm_5_vars_134107069309918455251112883047 : (((((False ∨ ((((((p3 → p3) ∨ p5) ∧ True) → (p5 ∧ (p1 ∨ False))) ∧ p4) → p4)) → p3) ∧ (p5 ∨ True)) ∨ True) ∨ ((p5 ∨ p3) ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148042888604632040972674756411 : (((True ∧ (False ∨ (((((True ∧ p1) → ((p4 → (p5 → True)) ∨ True)) → p2) → False) → p1))) ∨ (p5 → True)) ∨ (((True ∧ p5) → True) → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157059073410888454248207832083 : (((p4 ∧ (((p5 ∧ p4) ∧ True) ∧ (((True → p3) ∨ ((p3 → p2) ∨ (p4 ∧ p3))) → p4))) ∨ False) ∨ (p4 → (((p5 ∨ p5) ∧ p1) → p1))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323532876334026780101212249144 : (p5 ∨ ((p5 → (p3 ∧ (((p4 ∧ p1) ∨ ((p2 → (((p3 ∨ True) ∨ (True ∨ p1)) ∨ False)) ∧ p3)) ∧ (p1 → p3)))) ∨ ((p3 → True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89026965381282506442007121417 : ((((True → p4) ∧ True) ∧ (False → (p5 → ((p3 → p2) ∧ (False ∧ (p4 ∨ ((((True → p3) → (p1 → p4)) ∨ True) ∧ (True ∧ p4)))))))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254430444201998329959291528637 : ((p2 ∧ p5) → (p2 ∧ (((p2 → (((p3 ∨ ((False ∧ p3) ∨ (p4 → p2))) ∧ p4) ∨ (True ∧ False))) ∨ ((False → (p4 ∨ p5)) → p2)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701045133526786210993189915794 : ((((((p2 → ((p4 ∧ (p2 ∨ p2)) ∨ p2)) ∨ p3) → p2) ∧ (((p5 → p3) ∨ (p5 ∧ (p4 → p2))) ∧ ((False → (True ∨ p4)) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799943724504599314316466295450 : (((p2 → ((((p5 ∧ ((p1 → (((((p5 ∨ p3) → (p4 ∨ False)) → p1) ∨ (False ∨ p2)) → (p3 ∧ False))) ∧ True)) → p4) ∨ p4) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64302894384777385337389726603 : ((False ∨ (p5 → ((p5 → (False ∨ (False ∧ ((p4 ∨ p3) → (p3 → ((True → True) → p1)))))) ∨ (True ∧ (False ∨ ((False ∧ p4) ∧ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149860555630660946078057701278 : ((p2 ∨ (((((p2 ∨ False) ∨ ((True ∨ (p2 ∨ p4)) ∧ p3)) → p2) ∧ ((p2 ∨ (p4 ∧ p3)) → p2)) ∧ p3)) ∨ (p4 ∨ (True → (False → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_96407778783352422927187439064 : ((False ∨ (((((((((False ∧ (p1 ∨ p1)) → p5) ∨ False) → (p3 → False)) ∧ p4) → True) → p4) ∨ (True ∨ p5)) → (p2 ∧ (False ∨ p5)))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((((((((False ∧ (p1 ∨ p1)) → p5) ∨ False) → (p3 → False)) ∧ p4) → True) → p4) ∨ (True ∨ p5)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134922276892606807790545951784 : ((((p5 ∨ ((((p4 → (False → p4)) ∧ p4) ∨ True) ∧ ((((False ∨ p4) ∨ True) → p5) → p2))) ∨ p1) ∧ (False → p1)) ∨ ((True ∨ p2) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319552675640522310751867166348 : (p4 ∨ (((True → p3) ∨ (((p2 ∨ p1) ∨ (p3 ∧ p2)) ∧ p4)) ∨ ((False ∨ True) ∨ (((True → (False → p3)) ∧ (p1 ∧ (False → p2))) ∨ p3)))) := by
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
theorem thm_5_vars_47310067920227539543069774673 : (((((p5 ∨ False) → p2) ∨ ((False → p2) → (False ∧ ((p1 ∧ ((False ∨ p2) ∨ ((p4 ∨ False) ∨ p1))) → (True → p2))))) ∨ (p5 ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166751384684836207671204576820 : ((p4 → ((True ∧ False) ∨ ((True ∨ p4) ∧ (p3 ∨ (((p2 ∨ p5) ∧ p2) ∨ (p4 ∨ p3)))))) ∨ ((((p2 ∧ p2) → True) ∨ p4) ∧ (p1 → p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62504613069921369021338501789 : ((p3 ∧ (p2 ∧ (((p1 ∧ (p2 ∧ (p4 ∧ p2))) ∨ (((p2 → (p4 ∧ ((p1 ∨ (p4 ∨ False)) ∨ p4))) ∨ True) ∨ (p2 ∧ p5))) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662814408715484185426001740718 : ((((((True ∨ p2) ∨ False) ∧ (((p1 ∨ (p2 ∨ ((((p5 ∨ ((p5 → True) ∧ p1)) ∧ True) ∨ True) → True))) ∨ p5) ∨ p1)) → (p1 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151562735076192565867824352129 : ((((((p1 → ((p1 ∧ p1) ∧ (p3 ∨ p2))) → p5) ∨ ((False ∧ False) ∧ (p4 ∨ False))) → p5) → (p1 ∧ True)) → (p5 → (p5 ∨ (False → p5)))) := by
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
theorem thm_5_vars_49281528934432540539693910654 : (((p4 ∧ (((p5 ∧ ((p3 ∨ (p3 ∧ (p1 ∧ True))) ∧ (p3 ∨ p5))) ∧ (p1 → False)) ∨ (p5 ∨ (False ∨ p2)))) ∨ (p4 ∧ (p4 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591288947776374591943589564335 : ((((((((p5 → p1) ∧ p2) ∧ (False ∨ (True → ((False → p2) ∧ (p1 ∨ (p4 ∧ p4)))))) → ((p5 ∧ p5) ∧ p3)) ∧ (p2 ∧ True)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185194723718183327663610607262 : ((True ∧ ((p5 ∨ (p4 ∧ (((p1 ∨ p1) → p5) → True))) → p5)) ∨ ((((False ∧ p1) ∨ ((p4 ∨ (p2 ∨ p5)) → p1)) ∧ (p5 ∨ False)) → p1)) := by
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
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h9 : (p4 ∨ (p2 ∨ p5)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h10 := h7 h9
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614022545856013810073147718282 : ((((((True ∨ p2) ∧ (((p4 ∧ (((p2 → False) ∨ (p5 → p3)) ∨ p5)) ∧ (p4 → (p2 → False))) ∧ p4)) ∨ (False ∨ (False ∨ True))) ∨ p4) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663197484947627201531332675421 : (((((p4 → p1) ∧ (p1 → (((((p5 → (p2 ∧ (p1 → ((False → (True → p4)) ∨ p1)))) ∧ p3) ∧ p5) ∧ False) → False))) → (p2 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113966724210226785848645292892 : (((False ∧ (p2 ∨ ((((((p2 ∧ p5) ∧ (True ∧ p4)) → (p4 ∨ p5)) ∨ p5) ∧ p2) ∨ (p5 → False)))) ∧ (p3 ∨ (True → p4))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51821843972086985876183639423 : (((p1 → (p5 ∨ ((((p3 → (p2 ∨ p1)) → (p4 ∧ p4)) ∧ p3) ∧ (p3 ∨ p2)))) ∧ (((p3 ∧ p1) ∧ False) ∧ (True → (p1 → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190718050784569976508273452712 : (((((p2 ∧ p4) ∧ p5) ∨ (p3 ∨ p1)) ∧ (False ∨ True)) ∨ (p1 ∨ ((((p5 ∨ p4) ∧ p3) ∨ (p4 ∧ p2)) → (((p5 ∧ p3) → p3) → True)))) := by
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
theorem thm_5_vars_42738964455975179180840081898 : (((True → (((p1 ∧ p1) → (p5 ∧ ((True → (p1 ∧ p4)) ∧ (p5 ∧ ((p3 ∧ p2) → p3))))) → ((p4 ∨ p1) → (True → p5)))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247763656745295728497974361902 : ((p1 ∨ False) ∨ (p4 → (True → (((False ∧ ((((p1 ∨ (True ∨ ((p1 ∨ p5) ∧ p1))) ∧ False) ∧ False) ∨ p5)) ∧ True) ∨ ((False ∧ p4) ∨ p4))))) := by
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
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209095502697166309613772546089 : ((p2 ∨ (((True ∧ False) ∨ p1) → p5)) → (((p1 ∧ (p1 → (p3 ∧ p3))) ∨ ((((p3 ∧ False) ∨ p2) → True) → False)) → (p5 → (p5 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811622046413346161850709371883 : (((p5 → (p1 → ((((p3 ∧ p1) → ((((((p1 → True) ∨ (False ∧ (True → False))) → p4) ∨ p4) ∧ (False ∨ p2)) ∨ p3)) → False) ∨ p1))) ∨ p2) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119461379615169638934288662289 : ((p4 → (((p2 → p1) ∨ p5) → (((p1 → False) → (p5 ∧ p3)) → (((True ∨ (p1 ∨ p4)) → (p2 → p2)) → (False ∧ p5))))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259208568410851988091233938604 : ((False → False) → (((((((p5 → False) → p3) → False) ∨ (p5 → True)) ∨ (p2 ∧ True)) ∨ (p5 ∧ p3)) ∨ (True ∧ ((p3 → p1) ∨ (False ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179351201681756205618628683285 : ((p2 ∨ ((((((p5 → (p4 ∧ p1)) ∧ False) → True) ∧ p2) → False) ∧ False)) ∨ ((((((p2 ∨ p2) ∨ p5) ∨ p3) → p5) ∧ p4) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40515948036788476483389033022 : ((((p4 ∧ ((((p5 → p1) ∧ p4) → (p3 ∧ False)) ∨ (True ∨ (p1 ∨ (((p1 → (p4 ∨ True)) → p5) ∨ (p1 ∧ p5)))))) ∨ p4) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191760998788326546917949390861 : ((p1 ∨ ((p3 ∧ ((p2 ∨ (p4 ∧ p4)) ∨ p4)) ∧ p2)) ∨ (True ∨ ((p5 → ((p4 → p5) ∨ ((p4 ∨ (p5 ∧ (p1 ∧ p1))) ∨ p5))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802981119877774230080001918681 : (((p3 → ((((p2 ∨ (False → (p3 ∧ (False → ((((True ∨ True) → p5) ∨ (True → p4)) → p1))))) ∨ (p5 ∨ p2)) → (p5 → p1)) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124313693593138875437537563512 : ((((p2 ∨ p2) ∧ (p4 ∨ ((p2 ∨ p4) → p1))) ∧ ((((p2 ∨ p2) ∧ (True ∧ p2)) ∧ (p4 ∧ ((p5 ∧ False) → p4))) ∨ p2)) → (p3 ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h9.left
        let h12 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h12.left
          let h15 := h12.right
          -- Conjunctions on the left can always be decomposed.
          let h16 := h10.left
          let h17 := h10.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h12.left
          let h20 := h12.right
          -- Conjunctions on the left can always be decomposed.
          let h21 := h10.left
          let h22 := h10.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- Conjunctions on the left can always be decomposed.
        let h28 := h26.left
        let h29 := h26.right
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h30 =>
          -- Conjunctions on the left can always be decomposed.
          let h31 := h29.left
          let h32 := h29.right
          -- Conjunctions on the left can always be decomposed.
          let h33 := h27.left
          let h34 := h27.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h35 =>
          -- Conjunctions on the left can always be decomposed.
          let h36 := h29.left
          let h37 := h29.right
          -- Conjunctions on the left can always be decomposed.
          let h38 := h27.left
          let h39 := h27.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h40 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h41 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h42 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h43 =>
        -- Conjunctions on the left can always be decomposed.
        let h44 := h43.left
        let h45 := h43.right
        -- Conjunctions on the left can always be decomposed.
        let h46 := h44.left
        let h47 := h44.right
        -- Disjunctions on the left can always be decomposed.
        cases h46
        case inl h48 =>
          -- Conjunctions on the left can always be decomposed.
          let h49 := h47.left
          let h50 := h47.right
          -- Conjunctions on the left can always be decomposed.
          let h51 := h45.left
          let h52 := h45.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h53 =>
          -- Conjunctions on the left can always be decomposed.
          let h54 := h47.left
          let h55 := h47.right
          -- Conjunctions on the left can always be decomposed.
          let h56 := h45.left
          let h57 := h45.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h58 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h59 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h60 =>
        -- Conjunctions on the left can always be decomposed.
        let h61 := h60.left
        let h62 := h60.right
        -- Conjunctions on the left can always be decomposed.
        let h63 := h61.left
        let h64 := h61.right
        -- Disjunctions on the left can always be decomposed.
        cases h63
        case inl h65 =>
          -- Conjunctions on the left can always be decomposed.
          let h66 := h64.left
          let h67 := h64.right
          -- Conjunctions on the left can always be decomposed.
          let h68 := h62.left
          let h69 := h62.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h70 =>
          -- Conjunctions on the left can always be decomposed.
          let h71 := h64.left
          let h72 := h64.right
          -- Conjunctions on the left can always be decomposed.
          let h73 := h62.left
          let h74 := h62.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h75 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66506926775853392456892361629 : ((True → ((True → (True ∧ (((p5 ∨ ((p5 ∧ (p1 ∧ p2)) ∧ p2)) → ((p1 ∧ (True ∨ (p4 ∨ p4))) → True)) → (p1 → False)))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_23214745568799519220319701840 : (((False ∨ (p2 ∨ ((p5 ∧ True) → True))) → (p4 → (((((p2 ∧ p4) → (p4 ∧ (((False ∧ p5) ∧ p4) ∧ False))) ∨ p2) → p1) ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217237545102568721304228305889 : (((True ∧ (True ∨ p1)) ∨ p1) → (((p1 ∧ ((p1 → p3) ∨ p4)) ∨ False) ∨ (p3 ∨ (p2 → (((False → ((True ∨ True) → p2)) ∨ False) ∨ True))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48024243653863403508558024391 : (((((((p4 ∧ (p2 → p2)) ∨ (p3 → p3)) ∨ (p3 ∧ p1)) ∨ p1) → ((False → (p2 ∨ p3)) ∨ ((p3 ∧ False) ∧ True))) → (True → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228206836936611469194211683513 : ((p5 ∧ (False ∨ p2)) ∨ ((False → (p5 ∨ (p5 → False))) → ((p3 ∨ p4) ∨ (True ∨ ((p2 → (((p5 → p5) ∧ (p3 ∨ False)) → p1)) ∧ True))))) := by
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
theorem thm_5_vars_47958569300733894828410267512 : ((((p1 ∨ ((p3 ∨ ((True ∧ (p1 ∨ (((p1 ∧ p1) ∧ p5) ∨ True))) ∨ (p1 ∧ p2))) ∧ p5)) → (p2 ∨ (False ∧ p4))) → (p1 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692604577770918991195067545215 : (((((((p1 ∧ p2) ∨ (p1 ∧ p2)) ∧ (p2 ∧ p5)) ∨ (True ∧ (p5 → p5))) ∧ ((True ∨ ((True ∧ ((p3 ∧ False) ∨ p2)) → p4)) ∨ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205844730347042819233357557463 : (((p2 → p1) → ((p1 → False) ∨ False)) ∨ (p1 → ((p4 → p4) ∨ ((((p5 ∧ p4) ∧ (((p3 ∧ (p2 ∧ p4)) → p3) ∨ p5)) → p2) ∧ p5)))) := by
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
theorem thm_5_vars_159270258659149680043782631138 : ((p4 → ((p3 ∧ (((((p1 ∨ (p5 ∨ True)) ∧ p3) ∧ ((p3 ∧ p2) → True)) ∨ False) ∨ p3)) ∨ True)) ∨ ((p2 ∨ p2) → ((p2 ∨ False) ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46970752312696003703518050958 : (((((((p3 → ((p3 → (p1 ∨ (p2 → p2))) ∨ ((p5 → (p3 → True)) ∧ True))) → p1) ∧ (p5 ∧ False)) → p2) → p5) ∨ (True ∨ p1)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609988711865487817155899582284 : (((((((p2 → (((((((p1 ∨ p4) ∨ True) ∧ (True ∧ ((p4 ∧ False) ∧ True))) → p4) ∧ p1) ∧ True) ∧ p4)) ∧ True) ∧ p5) → p4) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690381817746058308514763469945 : ((((p5 → (((p3 → (p3 ∧ p2)) ∧ (((p3 → (False ∨ False)) → p4) ∧ p4)) → p1)) ∨ ((p4 ∧ p1) ∨ ((p4 ∨ p2) ∨ (p1 ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114890196029701979008677154151 : (((p5 ∧ (p1 → ((((((p3 → p1) → p2) → False) ∧ p4) → p2) → p5))) ∨ ((((p2 ∨ p1) → p1) ∧ (True → p4)) ∨ p1)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205287917182607983810735086888 : (((p1 ∧ (p3 → p3)) ∨ (p1 ∨ p1)) ∨ ((p5 → True) ∧ ((False ∨ False) ∨ (p2 → (True → (p1 ∨ ((((True → p1) ∧ p3) ∧ p3) → p1))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h9
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114272194409774158638258660604 : (((((p1 ∨ ((((p4 ∨ p1) ∧ p3) ∨ p2) ∨ (p2 → (False → (False ∨ p5))))) ∧ p3) ∨ p3) ∧ (p4 ∧ (p3 → (p3 → p1)))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723930374669452761114761607808 : ((((True ∧ (p3 → True)) ∧ (((((p2 ∧ (p3 → p3)) → p4) ∨ p5) ∨ (p3 ∧ (p4 → ((((False → p2) → p3) ∨ p5) ∧ p2)))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134857678037576093726407251776 : (((True → (((p4 → (p5 ∨ ((p1 → True) ∧ p4))) → ((False ∧ False) → p1)) ∧ ((p4 ∧ (p3 ∧ False)) ∧ p5))) → p4) ∨ (p4 ∧ (p1 ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146524829405169315723058813963 : ((p4 ∨ (p2 → ((p5 ∨ (((p4 ∨ p2) ∨ p2) ∨ ((p1 ∧ p4) ∨ p1))) ∧ ((p5 ∨ (p3 ∨ p1)) ∨ p2)))) ∧ (True ∧ (p5 → (p5 ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69290099716140512984328547709 : ((p5 → (True ∧ ((p3 ∧ ((((p2 ∨ (False → ((p1 → False) ∨ False))) ∨ p1) → p2) ∧ (p5 ∨ ((p3 ∧ False) ∧ (p4 → False))))) ∨ p5))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38034738110569831573889896348 : ((((((p1 → (p3 ∧ (True ∧ (((p5 → ((p1 ∧ ((p2 ∨ p3) → p1)) → False)) ∧ p4) ∧ p1)))) ∧ True) ∨ p4) → (True ∧ p1)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115003497857989994868106184907 : ((((False ∨ ((p5 ∨ p3) ∨ p5)) → (False → (p4 ∨ (p4 → p3)))) ∧ (p2 ∨ ((((False ∧ p2) ∨ False) ∧ (p5 → p3)) ∧ False))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45984051779549527393956670069 : ((((((((((p4 ∨ p5) ∧ True) → p2) ∨ False) ∧ p1) ∨ ((p3 ∧ ((p5 → p4) ∨ p2)) ∨ (p4 ∨ True))) ∨ p3) ∧ True) ∧ (False → p1)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246635937328723798686522629756 : ((p5 ∧ p3) ∨ (((p5 ∧ (True → True)) ∧ ((p3 ∨ (p4 ∨ (p4 ∨ (True ∨ ((p4 ∨ True) → True))))) ∨ False)) ∨ ((p4 ∧ p4) ∨ (p5 ∨ True)))) := by
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
theorem thm_5_vars_113594809792690888441849426742 : (((p5 ∧ (p3 → ((((True ∨ (p2 ∨ ((p3 ∧ p2) ∧ (p3 ∨ True)))) → False) ∧ ((False ∧ False) ∧ True)) ∨ True))) ∨ (p3 ∧ p5)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654725811259836512405032213803 : (((((((p3 ∨ False) ∧ ((((True ∨ (p5 → p4)) ∨ (p4 → (p3 → True))) ∧ p5) ∧ (p1 ∨ (True ∧ p2)))) ∨ False) → p1) ∨ (True ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66394689059862841943012926969 : ((p5 ∨ (True → ((p5 ∨ ((p3 → (False ∨ ((False ∨ ((p4 ∨ p1) ∨ p4)) ∧ p4))) ∧ p2)) ∨ (((p1 ∨ False) ∨ (p2 ∨ False)) ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190188863869223612562800821374 : (((False ∨ (p1 ∨ ((False ∨ (p3 ∨ p3)) ∨ p3))) ∧ False) ∨ (False → (True → ((p3 ∨ p3) ∨ (p1 ∨ (((p4 ∧ False) ∧ (p1 → p4)) ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319693089210601149297862357287 : (p4 ∨ ((((False ∧ p4) ∨ (False → True)) ∧ True) ∧ (((False ∧ ((p4 ∧ p3) ∧ p3)) ∧ p4) ∨ ((False ∧ (((p1 ∧ True) ∧ p1) ∧ p3)) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351062812758015570382943430 : (((False ∨ p3) ∨ ((p2 ∨ (p3 → ((False ∨ p2) ∨ p3))) ∨ ((p1 ∧ True) ∧ (((False → ((p5 ∧ p3) ∧ p5)) → p5) ∨ p3)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111832793085225877328702717864 : (((((p2 ∨ (True → (p1 → ((True → (p3 ∨ False)) ∨ (p5 → (True ∧ (p5 → p5))))))) ∧ p1) ∨ ((p1 ∨ p3) ∧ p4)) ∨ True) ∨ (True ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134003990722477048740245606886 : (((((p5 → p3) → (p4 → (p3 ∧ (((((True ∨ p1) ∧ True) ∧ ((p4 ∧ p3) ∧ p5)) ∧ p4) ∧ p3)))) ∧ p1) ∨ False) ∨ ((p1 → p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262230454712711551124777697918 : (True ∧ ((((False ∧ (p2 ∧ ((p1 → (((True ∨ (p5 ∨ False)) ∧ p4) ∨ p1)) → p5))) ∧ (p5 ∧ ((p3 → p5) ∨ p5))) ∨ (True ∨ p1)) ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157571663466102827746184219474 : ((((True → (False ∧ p2)) ∧ ((p2 → (p2 ∨ p1)) ∧ ((p3 → (p5 → p2)) ∧ p1))) → (p2 → p3)) ∨ (p2 ∨ ((p1 ∨ p5) → (p2 → p4)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h9
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149573285064665599740788219746 : ((p2 ∧ (p5 ∨ ((True ∨ ((((((p1 → p1) ∧ p5) → p2) → False) → True) → ((p1 ∨ p5) ∨ p5))) ∧ p3))) ∨ (p4 → (p3 ∨ (p5 ∨ p4)))) := by
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
theorem thm_5_vars_206314190719723391592972570189 : ((p1 ∨ ((True ∨ p5) → (True → p4))) ∨ (((((p4 → (True → p2)) ∧ p3) ∧ True) ∨ ((((p4 ∨ p4) ∧ True) → False) → p5)) → (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20264523019549838557530274573 : ((((p1 ∨ (p4 ∧ p4)) → ((p1 ∧ p5) ∧ (p1 ∧ (p3 → (p4 ∧ False))))) ∨ (False → ((p3 ∧ p2) ∧ ((p4 ∧ (p5 ∧ p3)) ∧ p1)))) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_918708311371875942127502980884 : ((((((p3 ∨ ((p1 ∨ p1) ∨ (((p1 ∨ True) → p3) → p4))) → False) ∨ False) ∧ ((True ∧ ((p4 ∧ p1) ∧ (p5 → p1))) ∨ (p3 ∨ p2))) → p2) ∧ True) := by
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
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h12 : (p3 ∨ ((p1 ∨ p1) ∨ (((p1 ∨ True) → p3) → p4))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h13 := h4 h12
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h16 : (p3 ∨ ((p1 ∨ p1) ∨ (((p1 ∨ True) → p3) → p4))) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h15
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h17 := h4 h16
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- One of the premise coincides with the conclusion.
        exact h18
  case inr h19 =>
    -- False on the left can always be used.
    apply False.elim h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171723361273798845254187955909 : (((((p1 ∨ ((p5 ∨ p1) ∧ False)) → ((p5 ∧ p1) ∧ (True → p5))) ∧ True) → p4) ∨ (False ∨ (True ∨ ((((p1 → True) ∨ p3) ∨ p3) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762355850256812537525320499972 : (((p3 ∧ (((p3 ∧ True) ∧ ((p5 ∨ p4) → (((True ∧ ((False ∨ True) → p4)) → (p2 ∧ p1)) ∨ (p1 ∨ p2)))) ∨ ((True ∧ True) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165524616043504458203895239085 : ((((True ∧ p3) → (((True ∨ p5) ∨ (p4 ∨ True)) ∧ True)) → (p2 ∧ ((True ∨ p1) ∧ p4))) ∨ ((True ∧ ((p1 → (p3 → True)) ∨ p5)) ∨ p4)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53281457388415163907069181099 : (((p4 ∧ (((p3 ∧ (p1 ∧ p5)) → (False → (True → False))) ∨ p4)) ∨ ((p4 ∨ p2) → (p4 → (((False ∨ (p3 → p3)) → p5) → p5)))) ∨ p1) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (False ∨ (p3 → p3)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h5
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : (False ∨ (p3 → p3)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h9
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173817263297660851072002223826 : (((False ∨ (((True ∨ p4) ∧ p2) ∨ (True → (p5 → (True ∨ (False ∧ False)))))) ∨ p3) → ((p5 ∨ ((p3 → (p2 ∨ (True → p3))) ∨ p4)) ∨ p1)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h8 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h9
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h10 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h12
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- One of the premise coincides with the conclusion.
        exact h12
  case inr h14 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h15
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111714121845195434695354551483 : (((((((p3 ∧ ((False ∧ False) → p4)) ∨ (p1 ∧ p1)) → p4) ∨ (((False ∨ (p3 ∧ False)) ∧ p1) ∨ (p4 → False))) → p1) ∨ True) ∨ (p5 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148651229569669520888605427282 : ((((p2 ∧ (True ∧ True)) ∧ (p4 ∧ (False ∨ False))) ∧ (((p3 ∨ ((p2 ∨ p2) → p2)) ∧ p2) ∧ (False ∧ p4))) ∨ (((False → p4) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61196345236474665686993708849 : ((False ∧ ((p3 ∨ p5) ∨ ((p2 ∧ (p2 ∨ p1)) ∨ (((p3 ∧ ((p2 → p1) ∨ p1)) → False) ∧ (True ∧ (p2 ∨ (True ∧ (p2 ∨ p5)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60178525752358161200579806328 : (((p5 ∨ p1) → ((p2 → (p3 → ((((((p1 ∨ p3) ∨ p5) ∨ True) ∨ True) → p5) ∧ (p1 → (p5 → False))))) ∨ (False → (False ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228441179367704036972449639849 : ((False ∨ (False ∨ False)) ∨ (((p5 ∧ (((p3 ∨ (((p3 ∧ p3) ∨ p2) ∨ p4)) → p5) ∨ True)) → ((p1 ∨ (p4 → True)) ∨ False)) ∨ (p1 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216442237508915477454847509463 : ((p4 → (False ∧ (p5 ∧ p3))) ∨ (p5 → (p3 ∨ (((True → (True ∨ p4)) ∨ (True ∧ p2)) → ((((p4 → p2) → (True → p3)) ∧ p2) ∨ True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40979590524765167412691266013 : (((((p1 ∨ True) → (((p2 ∧ ((p1 ∨ p4) ∧ p2)) ∧ (p2 ∨ True)) → (p5 ∧ (p5 ∧ (False ∧ (p3 → p1)))))) ∨ (False ∧ p2)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328404459342910640918274551387 : (True → ((((p5 → (True → (p2 → ((p3 → (p1 ∨ (False ∨ (p1 ∧ True)))) ∨ False)))) → p3) ∨ True) ∨ (p5 ∨ (p5 ∧ ((p2 ∧ True) → False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620715811719292475148933163452 : (((((p2 ∧ p4) → ((p3 → (True → (p3 ∧ ((((p4 ∨ True) ∧ (p1 → (False ∨ p1))) ∨ ((True ∨ p5) ∧ p4)) → p2)))) → False)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_67340227006774028135482710694 : ((p1 → (((p5 ∧ (((p2 ∨ True) ∧ p4) ∧ ((p3 → (p5 ∧ p1)) ∧ p5))) → ((((False ∧ p2) ∧ p2) ∨ p4) → (p1 → p3))) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



